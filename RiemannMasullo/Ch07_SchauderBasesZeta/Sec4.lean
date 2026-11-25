module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b
public import RiemannMasullo.Ch06_LocalGlobal.Sec3
public import RiemannMasullo.AppC_LCTVS.Sec3a

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import RiemannMasullo.Ch02_AdelicTheta.Sec2b
import RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Distribution.TemperedDistribution
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.OpenMapping
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.ChangeVariables
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec2
import RiemannMasullo.Ch02_AdelicTheta.Sec1
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
import Mathlib.Analysis.Normed.Group.Tannery
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Holomorphic
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3b

import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import all RiemannMasullo.Ch06_LocalGlobal.Sec3
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec3b

import RiemannMasullo.ForMathlib.Analysis.Meromorphic.VerticalStripZeros

/-! # §7.4 Nuclearity

The spectral quotient is in Schwartz–Bergman coordinates. The orbital quotients
use the quotient topology of the zero-moment homogeneous theta space.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 150000
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "ω(" χ ")" => (χ : U).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* C𝔽)
local notation "P" => adelePolarSubspace F
local notation "B" => SchwartzBergman (univ : Set ℝ)
local notation "Entire" => entireContinuousMapSubalgebra

local instance instIdeleClassT2Sec4 : T2Space C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1

local instance instIdeleClassLocallyCompactSec4 : LocallyCompactSpace C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1

local instance instIdeleClassMeasurableSec4 (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
local instance instNuclearitySecondCountable : SecondCountableTopology C𝔽 :=
  letI := idele_secondCountable F
  inferInstanceAs (SecondCountableTopology
    (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))

local notation "𝒟" => BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "Π(" χ ")" => LinearMap.ker ((homogeneousAdelicThetaLinearMap F (ω(χ))).domRestrict P)
local notation "Θ₀(" χ ")" => ↥P ⧸ Π(χ)
local notation "mkΘ(" χ ", " f ")" => (Submodule.Quotient.mk f : Θ₀(χ))
local notation "Z(" χ ", " τ ", " hτ ")" => (exists_globalPolarThetaMellin χ τ hτ).choose
local notation "testIntegrand(" χ ", " φ ", " s ")" =>
  (fun g : C𝔽 ↦ (φ : 𝒟).val g * (ideleClassNormTwist χ s) g)

/-- Paper: Equation (7.4.1.1), p. 366.
The class-group Mellin transform of a Bruhat test uses the norm twist of the given character
and the idèle-class Tamagawa measure. -/
def nuclearityTestMellin (χ : U) (φ : 𝒟) (s : ℂ) : ℂ :=
  ∫ g, testIntegrand(χ, φ, s) g ∂μ𝔽

/-- Paper: Equation (7.4.1.1), p. 366.
The test integral converges absolutely throughout the norm chart.
At the trivial quasi-character it gives the integral of the test. -/
theorem nuclearityTestMellin_integrable (χ : U) (φ : 𝒟) :
    (∀ s : ℂ, Integrable (testIntegrand(χ, φ, s)) μ𝔽) ∧
      nuclearityTestMellin 1 φ 0 = ∫ g, φ.val g ∂μ𝔽 := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hc : Continuous φ.val :=
    continuous_schwartzBruhat (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  constructor
  · intro s
    exact (hc.mul (ideleClassNormTwist χ s).continuous).integrable_of_hasCompactSupport
      (show HasCompactSupport φ.val from φ.property.2).mul_right
  · apply integral_congr_ae
    filter_upwards with g
    change φ.val g * (1 * _ ^ (0 : ℂ)) = φ.val g
    simp

/-- Absolute convergence on every norm line makes the Mellin multiplier entire. -/
private theorem archNuclearityDenominator_closed_invariant_multiplier
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (φ : 𝒟) :
    Differentiable ℂ (nuclearityTestMellin χ φ) := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let n := fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)
  let f := fun g : C𝔽 ↦ φ.val g * (χ g : ℂ)
  have hn : Continuous n :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have heq (s : ℂ) (g : C𝔽) : f g * (n g : ℂ) ^ s = testIntegrand(χ, φ, s) g :=
    mul_assoc _ _ _
  have h := analyticOnNhd_integral_mul_cpow_of_integrable μ𝔽 f n hn.measurable
    (fun g ↦ NNReal.coe_pos.mpr (Units.zero_lt _)) isOpen_univ
    (fun s _ ↦ by simpa only [heq] using (nuclearityTestMellin_integrable χ φ).1 s)
  have hfun : nuclearityTestMellin χ φ = fun s ↦ ∫ g, f g * (n g : ℂ) ^ s ∂μ𝔽 := by
    funext s
    simp only [heq, nuclearityTestMellin]
  rw [hfun]
  exact fun s ↦ (h s (mem_univ _)).differentiableAt

/-- Paper: Theorem 7.4.1.1(2), pp. 366–367.
An operator of order zero admits a nuclear presentation with rapidly decreasing
coefficients. The presentation includes equicontinuity and a common Banach disc. -/
def IsStronglyNuclearOperator {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    (A : E →L[ℂ] E) : Prop :=
  ∃ r : NuclearPresentation A, ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
    ‖r.coeff n‖ * ((n : ℝ) + 1) ^ k ≤ C

/-- Paper: Theorem 7.4.1.1(2), pp. 366–367.
Every continuous rank-one operator is of order zero. -/
theorem isStronglyNuclearOperator_rankOne {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
    (ℓ : StrongDual ℂ E) (x : E) : IsStronglyNuclearOperator (ℓ.smulRight x) := by
  obtain ⟨r, hr, _, _, htail⟩ := nuclearPresentation_smulRight ℓ x 1 one_ne_zero
  refine ⟨r, fun k ↦ ⟨1, ?_⟩⟩
  intro n
  cases n with
  | zero => simp [hr]
  | succ n => simp [htail n]

private theorem specDenom_mem_div (g : Entire) (φ : B) :
    φ ∈ schwartzBergmanDivisible g ↔
      ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, φ.val s = g.val s * u s := by
  rw [schwartzBergmanDivisible, Submodule.mem_comap, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a.val, a.property, fun s ↦ ?_⟩
    have h := congrArg (fun e : Entire ↦ e.val s) ha
    change a.val s * g.val s = (schwartzBergmanEntireInclusion φ).val s at h
    rw [schwartzBergmanEntireInclusion_apply] at h
    rw [← h, mul_comm]
  · rintro ⟨u, hu, h⟩
    refine ⟨⟨⟨u, hu.continuous⟩, hu⟩, ?_⟩
    apply Subtype.ext
    ext s
    change u s * g.val s = (schwartzBergmanEntireInclusion φ).val s
    rw [schwartzBergmanEntireInclusion_apply, h, mul_comm]

private theorem specDenom_B_ext (φ ψ : B) (h : ∀ s, φ.val s = ψ.val s) : φ = ψ :=
  Subtype.ext (funext h)

private theorem specDenom_shift_mem (φ : B) (c : ℂ) :
    (fun w ↦ φ.val (w - c)) ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
  obtain ⟨-, hd, hb⟩ := φ.property
  refine ⟨fun z hz ↦ absurd (mem_univ _) hz, ?_, ?_⟩
  · have hd' : Differentiable ℂ φ.val := fun z ↦
      (hd z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    exact (hd'.comp (differentiable_id.sub_const c)).differentiableOn
  · intro a b hab _ N
    obtain ⟨A, hA⟩ := hb (a - c.re) (b - c.re) (by linarith) (subset_univ _) N
    obtain ⟨A₀, hA₀⟩ := hb (a - c.re) (b - c.re) (by linarith) (subset_univ _) 0
    refine ⟨2 ^ N * (A + ‖c‖ ^ N * A₀), ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have hz : w - c ∈ Complex.re ⁻¹' Icc (a - c.re) (b - c.re) := by
      simp only [mem_preimage, mem_Icc, Complex.sub_re] at hw ⊢
      constructor <;> linarith [hw.1, hw.2]
    have h1 := hA ⟨w - c, hz, rfl⟩
    have h0 := hA₀ ⟨w - c, hz, rfl⟩
    simp only [pow_zero, one_mul] at h0
    change ‖(w - c) ^ N * φ.val (w - c)‖ ≤ A at h1
    change ‖w ^ N * φ.val (w - c)‖ ≤ _
    set z := w - c
    have hwz : w = z + c := by simp [z]
    rw [hwz, norm_mul, norm_pow]
    rw [norm_mul, norm_pow] at h1
    have hn : ‖z + c‖ ^ N ≤ 2 ^ N * (‖z‖ ^ N + ‖c‖ ^ N) := by
      calc ‖z + c‖ ^ N ≤ (‖z‖ + ‖c‖) ^ N := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) N
        _ ≤ (2 * max ‖z‖ ‖c‖) ^ N := by
          apply pow_le_pow_left₀ (by positivity)
          linarith [le_max_left ‖z‖ ‖c‖, le_max_right ‖z‖ ‖c‖]
        _ = 2 ^ N * max ‖z‖ ‖c‖ ^ N := mul_pow _ _ _
        _ ≤ 2 ^ N * (‖z‖ ^ N + ‖c‖ ^ N) := by
          gcongr
          rcases le_total ‖z‖ ‖c‖ with h | h
          · rw [max_eq_right h]; linarith [pow_nonneg (norm_nonneg z) N]
          · rw [max_eq_left h]; linarith [pow_nonneg (norm_nonneg c) N]
    calc ‖z + c‖ ^ N * ‖φ.val z‖ ≤ 2 ^ N * (‖z‖ ^ N + ‖c‖ ^ N) * ‖φ.val z‖ :=
          mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = 2 ^ N * (‖z‖ ^ N * ‖φ.val z‖ + ‖c‖ ^ N * ‖φ.val z‖) := by ring
      _ ≤ 2 ^ N * (A + ‖c‖ ^ N * A₀) := by
          gcongr

private theorem specDenom_gen_bwd {X Y Q Bm : Type*} (ι : X → Y) (q : Y → Q) (c : X → Q)
    (hc : Surjective c) (hcq : ∀ x, c x = q (ι x)) (ZB : Q → Bm) (S : Set Bm)
    (hr : Set.range ZB = S) (φ : Bm) (hφ : φ ∈ S) : ∃ x : X, ZB (q (ι x)) = φ := by
  rw [← hr] at hφ
  obtain ⟨y, rfl⟩ := hφ
  obtain ⟨x, rfl⟩ := hc y
  exact ⟨x, by rw [hcq]⟩

private theorem specDenom_gen_mem {M Q Bm : Type*} (mk : M → Q) (hmk : Surjective mk) (Zf : Q → Bm)
    (ev : Bm → ℂ → ℂ) (hev : Injective ev) (zf : M → ℂ → ℂ)
    (hspec : ∀ f s, ev (Zf (mk f)) s = zf f s) (G' : ℂ → ℂ)
    (hv : ∃ G : ℂ → ℂ, G' = G ∧
      (∀ f : M, ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, zf f s = G s * u s) ∧
      (∀ φ : Bm, (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev φ s = G s * u s) →
        ∃ f : M, ∀ s, ev φ s = zf f s)) (φ : Bm) :
    (∃ x, Zf x = φ) ↔ ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev φ s = G' s * u s := by
  obtain ⟨G, rfl, hfwd, hbwd⟩ := hv
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨f, rfl⟩ := hmk x
    obtain ⟨u, hu, h⟩ := hfwd f
    exact ⟨u, hu, fun s ↦ (hspec f s).trans (h s)⟩
  · intro h
    obtain ⟨f, hf⟩ := hbwd φ h
    exact ⟨mk f, hev (funext fun s ↦ (hspec f s).trans (hf s).symm)⟩

private theorem specDenom_gen_range_eq {Q Bm : Type*} {_ : AddCommGroup Q} {_ : Module ℂ Q}
    {_ : TopologicalSpace Q} {_ : AddCommGroup Bm} {_ : Module ℂ Bm} {_ : TopologicalSpace Bm}
    (Zc : Q →L[ℂ] Bm) (D : Submodule ℂ Bm) (h : ∀ φ, (∃ x, Zc x = φ) ↔ φ ∈ D) :
    Zc.toLinearMap.range = D := by
  ext φ
  rw [LinearMap.mem_range]
  exact h φ

private theorem specDenom_gen_shift {Q Bm : Type*} (Zf : Q → Bm) (ev : Bm → ℂ → ℂ) (L : ℂ → ℂ)
    (c : ℂ)
    (hrange : ∀ φ : Bm, (∃ x, Zf x = φ) ↔
      ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev φ s = L s * u s)
    (hshift : ∀ φ : Bm, ∃ ψ : Bm, ∀ w, ev ψ w = ev φ (w - c)) (f : Bm) :
    (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev f s = L (s + c) * u s) ↔
      ∃ x : Q, ∀ s, ev f s = ev (Zf x) (s + c) := by
  constructor
  · rintro ⟨u, hu, h⟩
    obtain ⟨ψ, hψ⟩ := hshift f
    obtain ⟨x, hx⟩ := (hrange ψ).mpr ⟨fun w ↦ u (w - c), hu.comp (differentiable_id.sub_const c),
      fun w ↦ by rw [hψ, h, sub_add_cancel]⟩
    exact ⟨x, fun s ↦ by rw [hx, hψ, add_sub_cancel_right]⟩
  · rintro ⟨x, hx⟩
    obtain ⟨u, hu, h⟩ := (hrange (Zf x)).mp ⟨x, rfl⟩
    exact ⟨fun s ↦ u (s + c), hu.comp (differentiable_id.add_const c), fun s ↦ by rw [hx, h]⟩

section Spectral

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

local notation "Λ(" χ ", " τ ", " hτ ")" => regularizedCompletedHeckeL χ τ hτ
  (continuedCompletedHeckeL χ) (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2

/-- Paper: Equation (7.4.0.1), p. 366.
In Mellin coordinates the norm-power twist shifts the regularized completed generator
by translation of the argument by a. The shifted generator is entire. -/
theorem spectralNuclearityGenerator_differentiable (a : ℝ) :
    Differentiable ℂ (fun s ↦ (Λ(χ, τ, hτ)).val (s + (a : ℂ))) := by
  exact (Λ(χ, τ, hτ)).property.comp (differentiable_id.add_const (a : ℂ))

/-- Paper: Equation (7.4.0.1), p. 366.
The denominator is the shifted theta image in the Schwartz–Bergman model of the
exponentially decaying isotype. -/
def spectralNuclearityDenominator (a : ℝ) : Submodule ℂ B :=
  let h := spectralNuclearityGenerator_differentiable χ τ hτ a
  schwartzBergmanDivisible ⟨⟨_, h.continuous⟩, h⟩

/-- Paper: Equation (7.4.0.1), p. 366.
This is the spectral quotient with its quotient topology, in Mellin coordinates. -/
abbrev SpectralNuclearityQuotient (a : ℝ) := B ⧸ spectralNuclearityDenominator χ τ hτ a

open Classical in
private theorem specDenom_Lambda_val :
    ⇑(Λ(χ, τ, hτ)).val = toMeromorphicNFOn (fun s ↦
      (s + ((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℂ) *
        Complex.I) ^ (if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0) *
      (1 - s - ((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℂ) *
        Complex.I) ^ (if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0) *
      continuedCompletedHeckeL χ s) univ := rfl


private theorem specDenom_hδ (hω : ¬ ω(χ) = 1) :
    ¬ χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
  intro h
  apply hω
  ext g
  exact congrArg Subtype.val (DFunLike.congr_fun h g)

private theorem specDenom_hδ' (hω : ω(χ) = 1) :
    χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
  ext g
  exact congrArg Subtype.val (DFunLike.congr_fun hω g)

open Classical in
private theorem specDenom_L0 (hδ : ¬ χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    ⇑(Λ(χ, τ, hτ)).val = continuedCompletedHeckeL χ := by
  rw [specDenom_Lambda_val, ite_eq_right_of_eq_false _ _ (eq_false hδ)]
  simp only [pow_zero, one_mul]
  exact toMeromorphicNFOn_eq_self.mpr (continuedCompletedHeckeL_spec χ).1

open Classical in
private theorem specDenom_L1 (t : ℝ) (hω : ω(χ) = 1)
    (ht : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U) (((t : ℝ) : ℂ) * Complex.I)) :
    ⇑(Λ(χ, τ, hτ)).val = toMeromorphicNFOn (fun s ↦ ((s + (t : ℂ) * Complex.I) *
      (1 - s - (t : ℂ) * Complex.I)) * continuedCompletedHeckeL χ s) univ := by
  have hphase := existsUnique_ideleNormSection_character_phase χ τ hτ
  have ht' : ∀ u : ℝ≥0ˣ, (χ (QuotientGroup.mk (τ u)) : ℂ) =
      (((u : ℝ≥0) : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) := by
    intro u
    have he := DFunLike.congr_fun ht (QuotientGroup.mk (τ u))
    change (χ (QuotientGroup.mk (τ u)) : ℂ) * _ ^ (0 : ℂ) =
      1 * ((((ideleNorm F (τ u)).val : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) at he
    rw [Complex.cpow_zero, mul_one, one_mul, hτ u] at he
    exact he
  have hx : hphase.exists.choose = t := hphase.unique hphase.exists.choose_spec ht'
  rw [specDenom_Lambda_val, hx, ite_eq_left_of_eq_true _ _ (eq_true (specDenom_hδ' χ hω))]
  simp only [pow_one]

open Classical in
private theorem specDenom_values :
    ∃ G : ℂ → ℂ, ⇑(Λ(χ, τ, hτ)).val = G ∧
      (∀ f : P, ∃ u : ℂ → ℂ, Differentiable ℂ u ∧
        ∀ s, globalIdelicZFunction f.val (ideleClassNormTwist χ s) = G s * u s) ∧
      (∀ φ : B, (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, φ.val s = G s * u s) →
        ∃ f : P, ∀ s, φ.val s = globalIdelicZFunction f.val (ideleClassNormTwist χ s)) := by
  by_cases hω : ω(χ) = 1
  · have h1 := (globalConverse_existsUnique_normTwist χ hω).exists
    obtain ⟨t, ht⟩ := h1
    have h2 := globalConverse_normTwist χ t ht
    obtain ⟨ZB, h3⟩ := h2
    have hZB := h3.2.2.1
    have hrange := h3.2.2.2.1
    refine ⟨_, specDenom_L1 χ τ hτ t hω ht, ?_, ?_⟩
    · intro f
      have hm : ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, (ZB f).val s =
          toMeromorphicNFOn (fun s ↦ ((s + (t : ℂ) * Complex.I) *
            (1 - s - (t : ℂ) * Complex.I)) * continuedCompletedHeckeL χ s) univ s * u s :=
        (Set.ext_iff.mp hrange (ZB f)).mp ⟨f, rfl⟩
      obtain ⟨u, hu, h⟩ := hm
      exact ⟨u, hu, fun s ↦ (hZB f s).symm.trans (h s)⟩
    · intro φ hφ
      have hm : φ ∈ Set.range ZB := (Set.ext_iff.mp hrange φ).mpr hφ
      obtain ⟨f, hf⟩ := hm
      refine ⟨f, fun s ↦ ?_⟩
      rw [← hf]
      exact hZB f s
  · have h2 := globalConverse_nontrivial χ hω
    obtain ⟨ZB, h3⟩ := h2
    have hZB := h3.2.1
    have hrange := h3.2.2
    refine ⟨_, specDenom_L0 χ τ hτ (specDenom_hδ χ hω), ?_, ?_⟩
    · intro f
      have hm : ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s,
          (ZB ((LinearMap.ker (homogeneousAdelicThetaLinearMap F (ω(χ)))).mkQ f.val)).val s =
          continuedCompletedHeckeL χ s * u s :=
        (Set.ext_iff.mp hrange _).mp ⟨_, rfl⟩
      obtain ⟨u, hu, h⟩ := hm
      exact ⟨u, hu, fun s ↦ (hZB f.val s).symm.trans (h s)⟩
    · intro φ hφ
      have hs0 := globalConverse_nontrivial_exact (F := F) _ hω
      have hs := hs0.surjective
      have hx := specDenom_gen_bwd (fun f : P ↦ f.val) _ _ hs (fun _ ↦ rfl) ZB _ hrange φ hφ
      obtain ⟨f, hf⟩ := hx
      refine ⟨f, fun s ↦ ?_⟩
      rw [← hf]
      exact hZB f.val s


private theorem specDenom_range_mem (φ : B) :
    (∃ x : Θ₀(χ), (Z(χ, τ, hτ)) x = φ) ↔
      ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, φ.val s = (Λ(χ, τ, hτ)).val s * u s :=
  specDenom_gen_mem (fun f : P ↦ (Submodule.Quotient.mk f : Θ₀(χ)))
    (Submodule.Quotient.mk_surjective _) (fun x ↦ (Z(χ, τ, hτ)) x) (fun φ : B ↦ φ.val)
    (fun φ ψ h ↦ specDenom_B_ext φ ψ fun s ↦ congrFun h s)
    (fun (f : P) s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s))
    (fun f s ↦ ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f s).2)
    (⇑(Λ(χ, τ, hτ)).val) (specDenom_values χ τ hτ) φ

private theorem specDenom_mem_D (a : ℝ) (f : B) :
    f ∈ spectralNuclearityDenominator χ τ hτ a ↔
      ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, f.val s = (Λ(χ, τ, hτ)).val (s + (a : ℂ)) * u s :=
  specDenom_mem_div _ f

/-- Paper: Equation (7.4.0.1), p. 366.
The unshifted denominator is precisely the image of the pole-free theta Mellin map. -/
theorem spectralNuclearityDenominator_zero :
    spectralNuclearityDenominator χ τ hτ 0 = (Z(χ, τ, hτ)).toLinearMap.range :=
  (specDenom_gen_range_eq (Z(χ, τ, hτ)) (spectralNuclearityDenominator χ τ hτ 0) fun φ ↦
    (specDenom_range_mem χ τ hτ φ).trans ((specDenom_mem_D χ τ hτ 0 φ).trans
      (exists_congr fun u ↦ and_congr_right fun _ ↦ forall_congr' fun s ↦ by
        rw [Complex.ofReal_zero, add_zero])).symm).symm

/-- Paper: Equation (7.4.0.1), p. 366.
The denominator consists precisely of the Mellin transforms of norm-twisted theta classes. -/
theorem mem_spectralNuclearityDenominator_iff (a : ℝ) (f : B) :
    f ∈ spectralNuclearityDenominator χ τ hτ a ↔
      ∃ x : Θ₀(χ), ∀ s : ℂ, f.val s = ((Z(χ, τ, hτ)) x).val (s + (a : ℂ)) :=
  (specDenom_mem_D χ τ hτ a f).trans
    (specDenom_gen_shift (fun x : Θ₀(χ) ↦ (Z(χ, τ, hτ)) x) (fun φ : B ↦ φ.val) (⇑(Λ(χ, τ, hτ)).val)
      (a : ℂ) (specDenom_range_mem χ τ hτ)
      (fun φ ↦ ⟨⟨_, specDenom_shift_mem φ (a : ℂ)⟩, fun _ ↦ rfl⟩) f)

/-- A fixed first factor defines a continuous map into the completed inductive tensor. -/
private theorem spectralNuclearityDenominator_isotypeModel_tensor
    {X Y Z : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    [UniformContinuousConstSMul ℂ (InductiveTensor X Y)]
    (e : UniformSpace.Completion (InductiveTensor X Y) ≃L[ℂ] Z) (u : X) :
    ∃ J : Y →L[ℂ] Z, ∀ p, J p = e (UniformSpace.Completion.coe' (α := InductiveTensor X Y) (u ⊗ₜ[ℂ] p)) := by
  let j : InductiveTensor X Y →L[ℂ] UniformSpace.Completion (InductiveTensor X Y) :=
    UniformSpace.Completion.toComplL
  let hs := withGeneratingSeminorms_spec (X ⊗[ℂ] Y)
    (fun q : {q : Seminorm ℂ (X ⊗[ℂ] Y) // (∀ x : X, Continuous (fun y : Y ↦ q (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : Y, Continuous (fun x : X ↦ q (x ⊗ₜ[ℂ] y)))} ↦ q.val)
  exact ⟨e.toContinuousLinearMap.comp (j.comp ⟨TensorProduct.mk ℂ X Y u,
    hs.continuous_of_continuous_comp (TensorProduct.mk ℂ X Y u) fun q ↦ q.property.1 u⟩), fun _ ↦ rfl⟩

/-- Lift a scalar logarithmic profile by its tensor with the inverse compact character. -/
private theorem spectralNuclearityDenominator_isotypeModel_lift
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (χ : PontryaginDual G) :
    let K := m.toMonoidHom.ker
    let ω := χ.comp (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)
    let E := modulatedDecayIsotype m univ (mem_univ 0) ω
    ∃ J : PositiveRealExponentialDecay univ →L[ℂ] E, ∀ p t,
      (J p).val.val (τ t) = p.val (Real.log (t.val : ℝ)) := by
  intro K ω E
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨oneK, hone⟩ := compact_schwartzBruhat_one (H := K)
  obtain ⟨M, hM⟩ := schwartzBruhat_mul_unitaryCharacter (A := K) ω⁻¹
  let u := M oneK
  have hu (k : K) : u k = ((χ k.val : ℂ))⁻¹ := by
    rw [hM, hone, mul_one]
    exact Circle.coe_inv _
  let : UniformContinuousConstSMul ℂ (InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay univ)) :=
    uniformContinuousConstSMul_of_continuousConstSMul _ _
  have hB := modulatedExponentialDecay_tensor_equiv m univ hm ordConnected_univ univ_nonempty τ hτ
  let D := ModulatedExponentialDecay m univ
  let Profile := PositiveRealExponentialDecay univ
  have hJ : ∃ J : Profile →L[ℂ] D, ∀ p (k : K) t,
      (J p).val (k.val * τ t) = ((χ k.val : ℂ))⁻¹ * p.val (Real.log (t.val : ℝ)) := by
    have h := spectralNuclearityDenominator_isotypeModel_tensor
      (X := SchwartzBruhat K) (Y := Profile) (Z := D) hB.choose u
    obtain ⟨J, hJ⟩ := h
    refine ⟨J, fun p k t ↦ ?_⟩
    let ev (w : D) := w.val (k.val * τ t)
    have he : ev (J p) = u k * p.val (Real.log (t.val : ℝ)) := by
      with_reducible_and_instances exact (congrArg ev (hJ p)).trans (hB.choose_spec u p k t)
    exact he.trans (congrArg (· * _) (hu k))
  obtain ⟨J, hJ⟩ := hJ
  have hmem (p : Profile) : J p ∈ E := by
    apply (mem_modulatedDecayIsotype_iff m ω univ (mem_univ _) _).mpr
    intro k g
    let v : K := ⟨g / τ (m g), by change m (g / τ (m g)) = 1; rw [map_div, hτ _, div_self']⟩
    have hv : v.val * τ (m g) = g := div_mul_cancel _ _
    have hk : (k⁻¹ * v : K).val * τ (m g) = k.val⁻¹ * g := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, hv]
    rw [← hk, hJ, show (J p).val g = _ from (congrArg (J p).val hv.symm).trans (hJ p v (m g))]
    change (↑(χ ((k.val)⁻¹ * v.val)) : ℂ)⁻¹ * _ = (χ k.val : ℂ) * (_ * _)
    rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv, mul_inv_rev, inv_inv]
    ac_rfl
  refine ⟨J.codRestrict E hmem, fun p t ↦ ?_⟩
  change (J p).val (τ t) = _
  have he := hJ p (1 : K) t
  simpa only [Subgroup.coe_one, one_mul, map_one, Circle.coe_one, inv_one] using he

/-- The compact character integral of an isotype vector is its section value when
the compact Haar measure has mass one. -/
private theorem spectralNuclearityDenominator_isotypeModel_average
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G) (χ : PontryaginDual G)
    (μ₁ : Measure m.toMonoidHom.ker) (hv : μ₁ univ = 1) :
    let K := m.toMonoidHom.ker
    let ω := χ.comp (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)
    let E := modulatedDecayIsotype m univ (mem_univ 0) ω
    ∀ (u : E) t, (∫ k : K, (χ k.val : ℂ) * u.val.val (k.val * τ t) ∂μ₁) = u.val.val (τ t) := by
  intro K ω E u t
  have hv' (k : K) : (χ k.val : ℂ) * u.val.val (k.val * τ t) = u.val.val (τ t) := by
    have he := (mem_modulatedDecayIsotype_iff m ω univ (mem_univ _) u.val).mp u.property k (k.val * τ t)
    change (ω k : ℂ) * u.val.val (k.val * τ t) = u.val.val (τ t)
    exact he.symm.trans (congrArg u.val.val (inv_mul_cancel_left k.val (τ t)))
  rw [integral_congr_ae (.of_forall hv'), integral_const, measureReal_def, hv, ENNReal.toReal_one, one_smul]

/-- The unitary phase on the positive reals is an imaginary power. -/
private theorem spectralNuclearityDenominator_isotypeModel_phase (ψ : PontryaginDual ℝ≥0ˣ) :
    ∃ b : ℝ, ∀ t, ψ t = Circle.exp (b * Real.log (t.val : ℝ)) := by
  let c := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ
  obtain ⟨z, ⟨hz0, hz⟩, -⟩ := existsUnique_unitaryComplexPower c (fun t ↦ Circle.norm_coe (ψ t))
  have hz' : (z.im : ℂ) * Complex.I = z := by apply Complex.ext <;> simp [hz0]
  refine ⟨z.im, fun t ↦ Circle.ext ((hz t).trans ?_)⟩
  have hpos : 0 < (t.val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt t)
  rw [Circle.coe_exp, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
    ← Complex.ofReal_log hpos.le]
  conv_lhs => rw [← hz']
  congr 1
  push_cast
  ring

/-- The compact average realizes the section profile of the isotype. Its inverse
inserts the inverse compact character in the split tensor product. -/
private theorem spectralNuclearityDenominator_isotypeModel_mellin
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (χ : PontryaginDual G) :
    let K := m.toMonoidHom.ker
    let ω := χ.comp (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)
    let E := modulatedDecayIsotype m univ (mem_univ 0) ω
    ∃ M : E ≃L[ℂ] SchwartzBergman univ, ∀ (u : E) (s : ℂ),
      let v (t : ℝ≥0ˣ) := u.val.val (τ t) * ((χ (τ t) : ℂ) * ((t.val : ℝ) : ℂ) ^ s)
      Integrable v positiveRealHaar ∧ (M u).val s = ∫ t, v t ∂positiveRealHaar := by
  intro K ω E
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ₁ : Measure K := Measure.haarMeasure ⊤
  have hμ₁ : μ₁ univ = 1 := Measure.haarMeasure_self
  let μ := canonicalModulatedHaar m hm
  let : μ.IsHaarMeasure := (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  have hμ := canonicalModulatedHaar_eq_map_prod m hm τ hτ μ₁ hμ₁
  obtain ⟨b, hb⟩ := spectralNuclearityDenominator_isotypeModel_phase (χ.comp τ)
  obtain ⟨A, F, T, e, hA, hF, _, he, hT⟩ := modulatedMellin_isotypicDiagram
    m hm hτ.surjective univ isOpen_univ ordConnected_univ univ_nonempty τ hτ μ₁ μ hμ χ b hb
  obtain ⟨J, hJ⟩ := spectralNuclearityDenominator_isotypeModel_lift m hm τ hτ χ
  have hp (u : E) (t : ℝ≥0ˣ) : (A u.val).val (Real.log (t.val : ℝ)) = u.val.val (τ t) :=
    (hA u.val t).trans (spectralNuclearityDenominator_isotypeModel_average m τ χ μ₁ hμ₁ u t)
  let R := A.comp E.subtypeL
  have hleft (u : E) : J (R u) = u := by
    refine Subtype.ext (Subtype.ext (funext fun g ↦ ?_))
    let k : K := ⟨τ (m g) / g, by change m (τ (m g) / g) = 1; rw [map_div, hτ _, div_self']⟩
    have hk : k.val⁻¹ * τ (m g) = g := by change (_ / _)⁻¹ * _ = _; rw [inv_div, div_mul_cancel]
    have hact (v : E) := (mem_modulatedDecayIsotype_iff m ω univ (mem_univ _) v.val).mp v.property k (τ (m g))
    change (J (R u)).val.val g = u.val.val g
    rw [← hk, hact, hact, hJ]
    exact congrArg ((ω k : ℂ) * ·) (hp u (m g))
  have hright (p : PositiveRealExponentialDecay univ) : R (J p) = p := by
    apply Subtype.ext
    funext x
    let t : ℝ≥0ˣ := Units.mk0 (Real.exp x).toNNReal (by positivity)
    have ht : Real.log (t.val : ℝ) = x := by
      change Real.log ((Real.exp x).toNNReal : ℝ) = x
      rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
    exact ht ▸ (hp (J p) t).trans (hJ p t)
  let r := ContinuousLinearEquiv.equivOfInverse R J hleft hright
  let scalarMellin := positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty
  let M := (r.trans scalarMellin).trans T.symm
  refine ⟨M, fun u s ↦ ?_⟩
  let avg (t : ℝ≥0ˣ) := ∫ k : K, (χ k.val : ℂ) * u.val.val (k.val * τ t) ∂μ₁
  have havg (t : ℝ≥0ˣ) : avg t = u.val.val (τ t) :=
    spectralNuclearityDenominator_isotypeModel_average m τ χ μ₁ hμ₁ u t
  have hval (t : ℝ≥0ˣ) : ((t.val : ℝ) : ℂ) ^ s * (χ (τ t) : ℂ) * avg t =
      u.val.val (τ t) * ((χ (τ t) : ℂ) * ((t.val : ℝ) : ℂ) ^ s) := by rw [havg]; ring
  have hsplit := modulatedMellin_split m hm hτ.surjective univ isOpen_univ ordConnected_univ
    univ_nonempty τ hτ μ₁ μ hμ χ u.val s (mem_univ _)
  have hFT : M u = F u.val := by
    apply T.injective
    change T (T.symm (scalarMellin (A u.val))) = _
    rw [T.apply_symm_apply, hT, he]
  exact ⟨hsplit.2.1.congr (.of_forall hval), (congrArg (fun H : SchwartzBergman univ ↦ H.val s) hFT).trans
    ((hF u.val s (mem_univ _)).trans (hsplit.2.2.trans (integral_congr_ae (.of_forall hval))))⟩

/-- Continuous integrable positive-real profiles are determined by their
integrals against the unitary powers. -/
private theorem spectralNuclearityDenominator_isotypeModel_unique (f h : ℝ≥0ˣ → ℂ)
    (hf : Continuous f) (hh : Continuous h) (hi : Integrable f positiveRealHaar)
    (hj : Integrable h positiveRealHaar)
    (he : ∀ z : ℂ, z.re = 0 →
      ∫ t : ℝ≥0ˣ, f t * ((t.val : ℝ) : ℂ) ^ z ∂positiveRealHaar =
        ∫ t : ℝ≥0ˣ, h t * ((t.val : ℝ) : ℂ) ^ z ∂positiveRealHaar) : f = h := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let : LocallyCompactSpace ℝ≥0ˣ := e.symm.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology ℝ≥0ˣ := e.symm.isEmbedding.secondCountableTopology
  let ev (x : ℝ≥0ˣ) : PontryaginDual ℝ≥0ˣ →* Circle :=
    { toFun := fun η ↦ η x, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
  have hsep : Injective ev := fun _ _ e ↦ pontryaginDual_pairing_separates.1 (funext (DFunLike.congr_fun e))
  have hzero : f - h =ᵐ[positiveRealHaar] 0 := by
    apply ae_eq_zero_of_integral_mul_circle_eq_zero ev (fun η ↦ η.continuous) hsep (hi.sub hj)
    intro η
    let c := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η
    obtain ⟨z, ⟨hz, hη⟩, _⟩ := existsUnique_unitaryComplexPower c (fun t ↦ Circle.norm_coe (η t))
    have iχ (q : ℝ≥0ˣ → ℂ) (hq : Continuous q) (i : Integrable q positiveRealHaar) :
        Integrable (fun t ↦ q t * (η t : ℂ)) positiveRealHaar :=
      i.norm.mono' (hq.mul (continuous_subtype_val.comp η.continuous)).aestronglyMeasurable
        (.of_forall fun t ↦ by rw [norm_mul, Circle.norm_coe, mul_one])
    have hc (t) : (η t : ℂ) = ((t.val : ℝ) : ℂ) ^ z := hη t
    change ∫ t, (f t - h t) * (η t : ℂ) ∂positiveRealHaar = 0
    simp_rw [sub_mul]
    rw [integral_sub (iχ f hf hi) (iχ h hh hj), sub_eq_zero]
    simpa only [hc] using he z hz
  exact sub_eq_zero.mp (Measure.eq_of_ae_eq hzero (hf.sub hh) continuous_const)

/-- Shifting the Mellin argument by a real exponent inserts the corresponding
norm power in the integrand of a polar homogeneous theta transform. -/
private theorem spectralNuclearityDenominator_isotypeModel_shift (hτ : RightInverse τ (ideleNorm F)) (a : ℝ) (f : P) (s : ℂ) :
    let σ (t : ℝ≥0ˣ) : C𝔽 := QuotientGroup.mk (τ t)
    let H (t : ℝ≥0ˣ) := ((((t.val : ℝ) ^ a : ℝ) : ℂ) * homogeneousAdelicTheta (ω(χ)) f.val (σ t)) *
      (χ (σ t) : ℂ)
    let v (t : ℝ≥0ˣ) := H t * ((t.val : ℝ) : ℂ) ^ s
    Integrable v positiveRealHaar ∧
      homogeneousThetaMellinIntegral τ (ω(χ)) f.val (ideleClassNormTwist χ (s + a)) = ∫ t, v t ∂positiveRealHaar := by
  intro σ H v
  let c := ideleClassNormTwist χ (s + a)
  have hc (t : ℝ≥0ˣ) : homogeneousAdelicTheta (ω(χ)) f.val (σ t) * c (σ t) = v t := by
    change _ * ((χ (σ t) : ℂ) * (((ideleNorm F (τ t)).val : ℝ) : ℂ) ^ (s + (a : ℂ))) =
      (((((t.val : ℝ) ^ a : ℝ) : ℂ) * _) * _) * _
    rw [hτ, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr t.ne_zero)),
      Complex.ofReal_cpow (NNReal.coe_nonneg _) a]
    ring
  have hi := homogeneousThetaMellinIntegral_integrable_on_component τ (ω(χ)) f.val hτ (Or.inl f.property) c
    ⟨mem_univ _, fun g ↦ normOneRestriction_unitaryChart (ideleClassNorm F)
      (isProperMap_ideleClassNorm F).continuous χ (s + a) g⟩
  exact ⟨hi.congr (.of_forall hc), integral_congr_ae (.of_forall hc)⟩

/-- Paper: Equation (7.4.0.1), p. 366.
The section Mellin transform identifies the decay isotype with the full
Schwartz–Bergman space and takes the norm-twisted theta image to the denominator.
The section integral uses the quotient Haar measure dt/t of §3.2. -/
theorem spectralNuclearityDenominator_isotypeModel (a : ℝ) :
    let m : C𝔽 →ₜ* ℝ≥0ˣ := continuousIdeleClassNorm F
    let E := modulatedDecayIsotype m (Set.univ : Set ℝ) (Set.mem_univ 0) (ω(χ))
    ∃ M : ↥E ≃L[ℂ] B,
      (∀ (u : E) s, (M u).val s = ∫ t : ℝ≥0ˣ,
        u.val.val (QuotientGroup.mk (τ t)) *
          ideleClassNormTwist χ s (QuotientGroup.mk (τ t)) ∂positiveRealHaar) ∧
      ∀ u : E, M u ∈ spectralNuclearityDenominator χ τ hτ a ↔
        ∃ f : P, ∀ g : C𝔽, u.val.val g =
          ((((ideleClassNorm F g).val : ℝ) ^ a : ℝ) : ℂ) *
            homogeneousAdelicTheta (ω(χ)) f.val g := by
  intro m E
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ := q.comp τ
  have hσ : RightInverse σ m := hτ
  have hm : IsModulation m := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one⟩
  obtain ⟨M, hM⟩ := spectralNuclearityDenominator_isotypeModel_mellin m hm σ hσ χ
  have hc (s : ℂ) (t : ℝ≥0ˣ) : ideleClassNormTwist χ s (σ t) =
      (χ (σ t) : ℂ) * ((t.val : ℝ) : ℂ) ^ s := by
    change (χ (σ t) : ℂ) * (((m (σ t)).val : ℝ) : ℂ) ^ s = _
    rw [hσ]
  refine ⟨M, fun u s ↦ (hM u s).2.trans (integral_congr_ae (.of_forall fun t ↦
    congrArg (u.val.val (σ t) * ·) (hc s t).symm)), fun u ↦ ?_⟩
  let profile (t : ℝ≥0ˣ) := u.val.val (σ t) * (χ (σ t) : ℂ)
  have hU (s : ℂ) : Integrable (fun t : ℝ≥0ˣ ↦ profile t * ((t.val : ℝ) : ℂ) ^ s) positiveRealHaar ∧
      (M u).val s = ∫ t : ℝ≥0ˣ, profile t * ((t.val : ℝ) : ℂ) ^ s ∂positiveRealHaar := by
    simpa only [profile, mul_assoc] using hM u s
  let w (g : C𝔽) := ((((m g).val : ℝ) ^ a : ℝ) : ℂ)
  let H (f : P) (t : ℝ≥0ˣ) := w (σ t) * homogeneousAdelicTheta (ω(χ)) f.val (σ t) * (χ (σ t) : ℂ)
  have hH (f : P) (s : ℂ) :
      Integrable (fun t : ℝ≥0ˣ ↦ H f t * ((t.val : ℝ) : ℂ) ^ s) positiveRealHaar ∧
      ((exists_globalPolarThetaMellin χ τ hτ).choose (Submodule.Quotient.mk f)).val (s + (a : ℂ)) =
        ∫ t : ℝ≥0ˣ, H f t * ((t.val : ℝ) : ℂ) ^ s ∂positiveRealHaar := by
    have h := spectralNuclearityDenominator_isotypeModel_shift χ τ hτ a f s
    have hw (t : ℝ≥0ˣ) : w (σ t) = (((t.val : ℝ) ^ a : ℝ) : ℂ) :=
      congrArg (fun x : ℝ≥0ˣ ↦ (((x.val : ℝ) ^ a : ℝ) : ℂ)) (hσ t)
    simp only [H, hw]
    exact ⟨h.1, ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f _).1.trans h.2⟩
  rw [mem_spectralNuclearityDenominator_iff]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have he : profile = H f := by
      have hu : Continuous u.val.val := by
        let z := modulatedExponentialDecayTwist m univ ⟨0, mem_univ _⟩ u.val
        exact (schwartzBruhat_continuous z).congr
          ((modulatedExponentialDecay_zeroTwist_injective m univ (mem_univ _)).2 u.val)
      have hχ : Continuous (fun t : ℝ≥0ˣ ↦ (χ (σ t) : ℂ)) :=
        continuous_subtype_val.comp (χ.continuous.comp σ.continuous)
      have hr : Continuous (fun t : ℝ≥0ˣ ↦ (((t.val : ℝ) ^ a : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp ((NNReal.continuous_coe.comp Units.continuous_val).rpow_const
          (fun t ↦ Or.inl (NNReal.coe_ne_zero.mpr t.ne_zero)))
      have hw (t : ℝ≥0ˣ) : w (σ t) = (((t.val : ℝ) ^ a : ℝ) : ℂ) := congrArg
        (fun x : ℝ≥0ˣ ↦ (((x.val : ℝ) ^ a : ℝ) : ℂ)) (hσ t)
      apply spectralNuclearityDenominator_isotypeModel_unique
      · exact (hu.comp σ.continuous).mul hχ
      · exact (((hr.congr fun t ↦ (hw t).symm).mul
          ((homogeneousAdelicTheta (ω(χ)) f.val).continuous.comp σ.continuous)).mul hχ)
      · simpa only [Complex.cpow_zero, mul_one] using (hU 0).1
      · simpa only [Complex.cpow_zero, mul_one] using (hH f 0).1
      · exact fun s _ ↦ (hU s).2.symm.trans ((hx s).trans (hH f s).2)
    have hsec (t : ℝ≥0ˣ) : u.val.val (σ t) = w (σ t) * homogeneousAdelicTheta (ω(χ)) f.val (σ t) :=
      mul_right_cancel₀ (Circle.coe_ne_zero _) (congrFun he t)
    refine ⟨f, fun g ↦ ?_⟩
    let k : m.toMonoidHom.ker := ⟨σ (m g) / g, by change m (σ (m g) / g) = 1; rw [map_div, hσ _, div_self']⟩
    have hk : k.val⁻¹ * σ (m g) = g := by change (_ / _)⁻¹ * _ = _; rw [inv_div, div_mul_cancel]
    have hr := (mem_modulatedDecayIsotype_iff m (ω(χ)) univ (mem_univ _) u.val).mp u.property k (σ (m g))
    have ht := homogeneousAdelicTheta_homogeneous (ω(χ)) f.val k (σ (m g))
    rw [hk] at hr ht
    change u.val.val g = w g * _
    rw [hr, ht, hsec, mul_left_comm, show w (σ (m g)) = w g from congrArg
      (fun x : ℝ≥0ˣ ↦ (((x.val : ℝ) ^ a : ℝ) : ℂ)) (hσ _)]
  · rintro ⟨f, hf⟩
    refine ⟨Submodule.Quotient.mk f, fun s ↦ (hU s).2.trans <| (_root_.Eq.trans ?_ (hH f s).2.symm)⟩
    apply integral_congr_ae (.of_forall fun t ↦ ?_)
    change (u.val.val (σ t) * _ ) * _ = ((w (σ t) * _) * _) * _
    rw [hf]
    rfl

private theorem spectralNuclearityDenominator_closed_invariant_mellinAux {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] (φ c : X → ℂ) (n : X → ℝ) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hc : Continuous c) (hn : Continuous n) (hpos : ∀ x, 0 < n x) :
    Differentiable ℂ (fun s : ℂ ↦ ∫ x, φ x * (c x * (n x : ℂ) ^ s) ∂μ) ∧
      ∀ a b : ℝ, ∃ C, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖∫ x, φ x * (c x * (n x : ℂ) ^ s) ∂μ‖ ≤ C := by
  have hjoint : Continuous (fun p : ℂ × X ↦ ((n p.2 : ℂ)) ^ p.1) :=
    Continuous.cpow (Complex.continuous_ofReal.comp (hn.comp continuous_snd)) continuous_fst
      (fun p ↦ Complex.ofReal_mem_slitPlane.2 (hpos p.2))
  have hφi : Integrable φ μ := hφ.integrable_of_hasCompactSupport hφc
  have hpow (s : ℂ) : Continuous (fun x ↦ (n x : ℂ) ^ s) :=
    hjoint.comp (continuous_const.prodMk continuous_id)
  have hlog : Continuous (fun x ↦ Complex.log (n x : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuousOn_log.comp_continuous hn
      fun x ↦ (hpos x).ne') |>.congr fun x ↦ Complex.ofReal_log (hpos x).le
  constructor
  · intro s₀
    obtain ⟨C, hC⟩ := ((isCompact_closedBall s₀ 1).prod hφc).exists_bound_of_continuousOn
      (f := fun p : ℂ × X ↦ c p.2 * ((n p.2 : ℂ) ^ p.1 * Complex.log (n p.2 : ℂ)))
      ((hc.comp continuous_snd).mul (hjoint.mul (hlog.comp continuous_snd))).continuousOn
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun s x ↦ φ x * (c x * (n x : ℂ) ^ s))
      (F' := fun s x ↦ φ x * (c x * ((n x : ℂ) ^ s * Complex.log (n x : ℂ))))
      (x₀ := s₀) (bound := fun x ↦ ‖φ x‖ * C) (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s ↦ (hφ.mul (hc.mul (hpow s))).aestronglyMeasurable)
      ((hφ.mul (hc.mul (hpow s₀))).integrable_of_hasCompactSupport hφc.mul_right)
      (hφ.mul (hc.mul ((hpow s₀).mul hlog))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x s hs ↦ by
        by_cases hx : x ∈ tsupport φ
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (hC (s, x) ⟨Metric.ball_subset_closedBall hs, hx⟩) (norm_nonneg _)
        · simp [image_eq_zero_of_notMem_tsupport hx])
      (hφi.norm.mul_const C)
      (Filter.Eventually.of_forall fun x s _ ↦ by
        have h := (hasDerivAt_id s).const_cpow (c := (n x : ℂ))
          (Or.inl (Complex.ofReal_ne_zero.2 (hpos x).ne'))
        simpa only [id, mul_one] using (h.const_mul (c x)).const_mul (φ x))
    exact key.2.differentiableAt
  · intro a b
    obtain ⟨C, hC⟩ := hφc.isCompact.exists_bound_of_continuousOn
      (f := fun x ↦ ‖c x‖ * (n x ^ a + n x ^ b))
      ((hc.norm.mul ((hn.rpow_const fun x ↦ Or.inl (hpos x).ne').add
        (hn.rpow_const fun x ↦ Or.inl (hpos x).ne'))).continuousOn)
    refine ⟨∫ x, ‖φ x‖ * C ∂μ, fun s ha hb ↦ ?_⟩
    refine norm_integral_le_of_norm_le (hφi.norm.mul_const C) (Filter.Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ tsupport φ
    · rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hpos x)]
      have hp : n x ^ s.re ≤ n x ^ a + n x ^ b := by
        rcases le_total 1 (n x) with h1 | h1
        · exact (Real.rpow_le_rpow_of_exponent_le h1 hb).trans
            (le_add_of_nonneg_left (Real.rpow_nonneg (hpos x).le _))
        · exact (Real.rpow_le_rpow_of_exponent_ge (hpos x) h1 ha).trans
            (le_add_of_nonneg_right (Real.rpow_nonneg (hpos x).le _))
      have h := hC x hx
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _)
        (add_nonneg (Real.rpow_nonneg (hpos x).le _) (Real.rpow_nonneg (hpos x).le _)))] at h
      calc ‖φ x‖ * (‖c x‖ * n x ^ s.re) ≤ ‖φ x‖ * (‖c x‖ * (n x ^ a + n x ^ b)) := by gcongr
        _ ≤ ‖φ x‖ * C := by gcongr
    · simp [image_eq_zero_of_notMem_tsupport hx]

private theorem spectralNuclearityDenominator_closed_invariant_mellin (χ : U) (φ : 𝒟) :
    Differentiable ℂ (nuclearityTestMellin χ φ) ∧
      ∀ a b : ℝ, ∃ C, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖nuclearityTestMellin χ φ s‖ ≤ C := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hc : Continuous φ.val :=
    continuous_schwartzBruhat (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  have hn : Continuous (fun g : C𝔽 ↦ (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  exact spectralNuclearityDenominator_closed_invariant_mellinAux μ𝔽 φ.val (fun g ↦ (χ g : ℂ))
    (fun g : C𝔽 ↦ (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)) hc φ.property.2
    (continuous_subtype_val.comp χ.continuous) hn
    (fun g ↦ NNReal.coe_pos.2 (pos_iff_ne_zero.2 (Units.ne_zero _)))

private theorem spectralNuclearityDenominator_closed_invariant_mem (m : ℂ → ℂ)
    (hm : Differentiable ℂ m)
    (hb : ∀ a b : ℝ, ∃ C, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖m s‖ ≤ C) (f : ℂ → ℂ)
    (hf : f ∈ schwartzBergmanSubmodule (univ : Set ℝ)) :
    (fun s ↦ m s * f s) ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
  obtain ⟨-, hd, hbd⟩ := hf
  refine ⟨fun z hz ↦ absurd (mem_univ _) hz, hm.differentiableOn.mul hd, ?_⟩
  intro a b hab hI N
  obtain ⟨A, hA⟩ := hbd a b hab hI N
  obtain ⟨C, hC⟩ := hb a b
  refine ⟨max C 0 * A, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have h1 : ‖z ^ N * f z‖ ≤ A := hA ⟨z, hz, rfl⟩
  change ‖z ^ N * (m z * f z)‖ ≤ _
  rw [mul_left_comm, norm_mul]
  exact mul_le_mul (le_max_of_le_left (hC z hz.1 hz.2)) h1 (norm_nonneg _) (le_max_right _ _)

private theorem spectralNuclearityDenominator_closed_invariant_trace (m f : ℂ → ℂ) (a : ℝ)
    (N : ℕ) (C : ℝ) (hC : ∀ s : ℂ, s.re = a → ‖m s‖ ≤ C) (hc : Continuous (fun s ↦ m s * f s))
    (hf : MemLp (weightedVerticalTrace a N f) 2 volume) :
    (eLpNorm (weightedVerticalTrace a N (fun s ↦ m s * f s)) 2 volume).toReal ≤
      max C 0 * (eLpNorm (weightedVerticalTrace a N f) 2 volume).toReal := by
  have hz : Continuous (fun x : ℝ ↦ (a : ℂ) + (x : ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hmeas : AEStronglyMeasurable (weightedVerticalTrace a N (fun s ↦ m s * f s)) volume :=
    ((hz.pow N).mul (hc.comp hz)).aestronglyMeasurable
  let c : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have h := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (c := c) hmeas
    (g := weightedVerticalTrace a N f) (Filter.Eventually.of_forall fun x ↦ by
      rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnNorm, coe_nnNorm]
      change ‖((a : ℂ) + (x : ℂ) * Complex.I) ^ N * (m _ * f _)‖ ≤
        max C 0 * ‖((a : ℂ) + (x : ℂ) * Complex.I) ^ N * f _‖
      rw [mul_left_comm, norm_mul]
      exact mul_le_mul_of_nonneg_right (le_max_of_le_left (hC _ (by simp))) (norm_nonneg _)) 2
  have hne : c • eLpNorm (weightedVerticalTrace a N f) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hf.eLpNorm_ne_top
  refine (ENNReal.toReal_mono hne h).trans_eq ?_
  rw [ENNReal.toReal_smul, NNReal.smul_def, smul_eq_mul]
  rfl

private theorem spectralNuclearityDenominator_closed_invariant_cont {X ι : Type*}
    [AddCommGroup X] [Module ℂ X] (p : SeminormFamily ℂ X ι)
    (L : WithGeneratingSeminorms X p →ₗ[ℂ] WithGeneratingSeminorms X p)
    (h : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, p i (L x) ≤ C * p i x) : Continuous L :=
  WithSeminorms.continuous_of_isBounded (withGeneratingSeminorms_spec X p)
    (withGeneratingSeminorms_spec X p) L (Seminorm.IsBounded.of_real fun i ↦ by
      obtain ⟨C, hC0, hC⟩ := h i
      exact ⟨{i}, C, fun x ↦ (hC x).trans (mul_le_mul_of_nonneg_left
        (Seminorm.le_def.mp (Finset.le_sup (f := p) (Finset.mem_singleton_self i)) x) hC0)⟩)

/-- Paper: Theorem 7.4.1.1(1), p. 366.
The twisted theta image is closed. Compactly supported Bruhat tests act by continuous
Mellin multiplication, which preserves that image. -/
theorem spectralNuclearityDenominator_closed_invariant (a : ℝ) (φ : 𝒟) :
    let D := spectralNuclearityDenominator χ τ hτ a
    IsClosed (D : Set B) ∧
      ∃ A : B →L[ℂ] B,
        (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) ∧
        Set.MapsTo A (D : Set B) D := by
  intro D
  obtain ⟨hMd, hMb⟩ := spectralNuclearityDenominator_closed_invariant_mellin χ φ
  refine ⟨schwartzBergmanDivisible_isClosed _, ?_⟩
  let L : B →ₗ[ℂ] B :=
    { toFun := fun f ↦ ⟨fun s ↦ nuclearityTestMellin χ φ s * f.val s,
        spectralNuclearityDenominator_closed_invariant_mem _ hMd hMb f.val f.property⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun s ↦ mul_add _ _ _)
      map_smul' := fun c f ↦ Subtype.ext (funext fun s ↦ mul_left_comm _ _ _) }
  have hL : Continuous L := by
    refine spectralNuclearityDenominator_closed_invariant_cont _ L fun i ↦ ?_
    obtain ⟨C, hC⟩ := hMb i.1.val i.1.val
    refine ⟨max C 0, le_max_right _ _, fun f ↦ ?_⟩
    have hfc : Continuous (f.val : ℂ → ℂ) := continuousOn_univ.mp (f.property.2.1.continuousOn.mono fun _ _ ↦ trivial)
    exact spectralNuclearityDenominator_closed_invariant_trace _ f.val i.1.val i.2 C
      (fun s hs ↦ hC s hs.ge hs.le) (hMd.continuous.mul hfc)
      (schwartzBergman_trace_memLp _ i.1 2 (by norm_num) (by norm_num) i.2 f)
  refine ⟨⟨L, hL⟩, fun f s ↦ rfl, ?_⟩
  intro f hf
  obtain ⟨u, hu, h⟩ := (specDenom_mem_D χ τ hτ a f).mp hf
  refine (specDenom_mem_D χ τ hτ a _).mpr ⟨fun s ↦ nuclearityTestMellin χ φ s * u s, hMd.mul hu,
    fun s ↦ ?_⟩
  change nuclearityTestMellin χ φ s * f.val s = _
  rw [h s]
  ring

local notation "zeros(" χ ", " τ ", " hτ ")" =>
  {z : ℂ // 0 < analyticOrderAt ((Λ(χ, τ, hτ)).val : ℂ → ℂ) z}
local notation "multiplicity(" χ ", " τ ", " hτ ", " z ")" =>
  (analyticOrderAt ((Λ(χ, τ, hτ)).val : ℂ → ℂ) (z : ℂ)).toNat
local notation "jets(" χ ", " τ ", " hτ ")" =>
  Σ z : zeros(χ, τ, hτ), Fin (multiplicity(χ, τ, hτ, z))
local notation "Q(" a ")" => SpectralNuclearityQuotient χ τ hτ a
local notation "D(" a ")" => spectralNuclearityDenominator χ τ hτ a

private theorem exists_spectralNuclearityBiorthogonal_vanish (G u f : ℂ → ℂ)
    (hG : Differentiable ℂ G) (hu : Differentiable ℂ u) (a : ℂ)
    (hf : ∀ s, f s = G (s + a) * u s) (z : ℂ) (k : ℕ)
    (hk : k < (analyticOrderAt G z).toNat) : iteratedDeriv k f (z - a) = 0 := by
  have hg : AnalyticAt ℂ (fun s ↦ s + a) (z - a) := by fun_prop
  have hd : deriv (fun s ↦ s + a) (z - a) ≠ 0 := by simp
  have hcomp : analyticOrderAt (G ∘ fun s ↦ s + a) (z - a) = analyticOrderAt G z := by
    rw [analyticOrderAt_comp_of_deriv_ne_zero hg hd, sub_add_cancel]
  have hfe : f = (G ∘ fun s ↦ s + a) * u := funext fun s ↦ hf s
  have hGa : AnalyticAt ℂ (G ∘ fun s ↦ s + a) (z - a) :=
    (hG.comp (differentiable_id.add_const a)).analyticAt _
  have hua : AnalyticAt ℂ u (z - a) := hu.analyticAt _
  have hord : analyticOrderAt f (z - a) =
      analyticOrderAt G z + analyticOrderAt u (z - a) := by
    rw [hfe, analyticOrderAt_mul hGa hua, hcomp]
  have hle : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f (z - a) := by
    rw [hord]
    refine le_trans ?_ le_self_add
    cases h : analyticOrderAt G z with
    | top => exact le_top
    | coe n =>
      rw [h] at hk
      exact_mod_cast (show k + 1 ≤ n by simpa using hk)
  have hfa : AnalyticAt ℂ f (z - a) := by rw [hfe]; exact hGa.mul hua
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hfa).mp hle k (Nat.lt_succ_self k)

open Classical in
/-- Paper: Theorem 7.4.1.1(2), p. 366, using Theorem 7.1.4.2(3).
For each jet index there is a Schwartz–Bergman function whose derivative jets at the
shifted zeros of the regularized completed generator are the corresponding coordinate vector:
the `i.2`-th derivative at `i.1 − a` is `1` for `i = j` and `0` for every other jet index. -/
theorem exists_spectralNuclearityBiorthogonal_vectors (a : ℝ) (j : jets(χ, τ, hτ)) :
    ∃ f : B, ∀ i : jets(χ, τ, hτ),
      iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ)) = if i = j then 1 else 0 := by
  classical
  have h := orbitalSchwartzBergman_biorthogonal χ τ hτ (continuedCompletedHeckeL χ)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2 ∅
  rw [orbitalHeckeGenerator_empty] at h
  obtain ⟨b,hb⟩ := h
  let J := {p : ℂ × ℕ // (p.2 : ℕ∞) < analyticOrderAt ((Λ(χ,τ,hτ)).val : ℂ → ℂ) p.1}
  have emb {r : ℕ} {n : ℕ∞} (hr : r < n.toNat) : (r : ℕ∞) < n := by
    cases n using ENat.recTopCoe with
    | top => exact ENat.natCast_lt_top r
    | coe n => exact_mod_cast (by simpa using hr : r < n)
  let idx (i : jets(χ,τ,hτ)) : J := ⟨(i.1.val,i.2.val),emb i.2.isLt⟩
  have hinj : Injective idx := by
    rintro ⟨z,k⟩ ⟨w,l⟩ h
    have ez : z = w := Subtype.ext (congrArg (fun x : J ↦ x.val.1) h)
    subst w
    have ek : k = l := Fin.ext (congrArg (fun x : J ↦ x.val.2) h)
    subst l
    rfl
  let g := b (idx j)
  refine ⟨⟨fun s ↦ g.val (s - -(a:ℂ)),specDenom_shift_mem g (-a)⟩,fun i ↦ ?_⟩
  change iteratedDeriv i.2.val (fun s ↦ g.val (s - -(a:ℂ))) (i.1.val-(a:ℂ)) = _
  rw [iteratedDeriv_comp_sub_const]
  change iteratedDeriv i.2.val g.val ((i.1.val-(a:ℂ))- -(a:ℂ)) = _
  rw [sub_neg_eq_add,sub_add_cancel]
  simpa only [hinj.eq_iff] using hb (idx i) (idx j)

open Classical in
/-- Paper: Theorem 7.4.1.1(2), p. 366, using Theorem 7.1.4.2(3).
The jet functionals and their full biorthogonal families transport to the shifted
quotient. A zero z of the unshifted generator has its jets at z − a. -/
theorem exists_spectralNuclearityBiorthogonal (a : ℝ) :
    ∃ (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a))) (b : jets(χ, τ, hτ) → Q(a)),
      (∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) ∧
      ∀ i j, d i (b j) = if i = j then 1 else 0 := by
  choose b hb using exists_spectralNuclearityBiorthogonal_vectors χ τ hτ a
  let J : jets(χ, τ, hτ) → B →L[ℂ] ℂ := fun i ↦
    (entireJet (i.1.val - (a : ℂ)) i.2.val).comp schwartzBergmanEntireInclusion
  have hJv (i : jets(χ, τ, hτ)) (f : B) :
      J i f = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ)) :=
    congrArg (fun g ↦ iteratedDeriv i.2.val g (i.1.val - (a : ℂ)))
      (funext (schwartzBergmanEntireInclusion_apply f))
  have hJ (i : jets(χ, τ, hτ)) : D(a) ≤ (J i).ker := fun f hf ↦ by
    obtain ⟨u, hu, h⟩ := (specDenom_mem_D χ τ hτ a f).mp hf
    refine LinearMap.mem_ker.mpr ((hJv i f).trans ?_)
    exact exists_spectralNuclearityBiorthogonal_vanish _ u f.val (Λ(χ, τ, hτ)).property hu
      (a : ℂ) h i.1.val i.2.val i.2.isLt
  refine ⟨fun i ↦ (D(a)).liftQL (J i) (hJ i), fun j ↦ (D(a)).mkQ (b j),
    fun i f ↦ hJv i f, fun i j ↦ (hJv i (b j)).trans (hb j i)⟩

section SpectralTraceEstimates

open Filter
open scoped SchwartzMap FourierTransform ContDiff
local notation "C₁" => (ideleClassNorm F).ker
local notation "σ₀(" r ")" => (QuotientGroup.mk (canonicalIdeleNormSection F
  (Units.mk0 (Real.exp r).toNNReal (by positivity))) : C𝔽)

private theorem spectralNuclearity_trace_section_norm (r : ℝ) :
    ideleClassNorm F (σ₀(r)) =
      Units.mk0 (Real.exp r).toNNReal (by positivity) :=
  canonicalIdeleNormSection_rightInverse F _

private theorem spectralNuclearity_trace_coset_norm (r : ℝ) (h : C₁) :
    (((ideleClassNorm F (σ₀(r) * h.val)).val : ℝ≥0) : ℝ) = Real.exp r := by
  rw [map_mul, show ideleClassNorm F h.val = 1 from h.property, mul_one, spectralNuclearity_trace_section_norm,
    Units.val_mk0, Real.coe_toNNReal _ (Real.exp_pos r).le]

/-- A Schwartz–Bruhat function on a group identified with the positive real line has a Schwartz
profile in logarithmic coordinates. -/
private theorem spectralNuclearity_trace_schwartz_log {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (d : G ≃ₜ* ℝ≥0ˣ) (f : SchwartzBruhat G) :
    ∃ b : 𝓢(ℝ, ℂ), ∀ x : G, b (Real.log ((d x).val : ℝ)) = f x := by
  let m : G →ₜ* ℝ≥0ˣ := ⟨d.toMulEquiv.toMonoidHom, d.continuous⟩
  let s : ℝ≥0ˣ →ₜ* G := ⟨d.symm.toMulEquiv.toMonoidHom, d.symm.continuous⟩
  have hm : IsModulation m := ⟨d.toHomeomorph.isProperMap, by
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨d.symm t, fun h ↦ ht ((d.apply_symm_apply t).symm.trans h)⟩⟩
  let : MeasurableSpace G := borel _
  let : BorelSpace G := ⟨rfl⟩
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology G := d.toHomeomorph.isEmbedding.secondCountableTopology
  let K := m.toMonoidHom.ker
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ : Measure K := Measure.haar
  let proj := schwartzBruhatIsotypicProjector m hm μ 1
  have hPf (u : SchwartzBruhat G) : proj u = u := by
    apply schwartzBruhatIsotypicProjector_apply_isotype
    apply (mem_actionIsotype _ _ _).2
    intro k
    have hk : (k : G) = 1 := d.injective (k.property.trans d.map_one.symm)
    change schwartzBruhatTranslationAction (G := G) (k : G) u = ((1 : PontryaginDual K) k : ℂ) • u
    rw [hk, map_one, PontryaginDual.one_apply, Circle.coe_one, one_smul]
    rfl
  obtain ⟨w, e, hw, he⟩ := schwartzBruhat_positiveReal_isotype_equiv m hm μ s d.apply_symm_apply 1
  let v := e.symm (proj.ker.mkQ f)
  have h : proj.ker.mkQ (w v) = proj.ker.mkQ f := (he v).symm.trans (e.apply_symm_apply _)
  have hmem := (Submodule.Quotient.eq _).mp h
  change proj (w v - f) = 0 at hmem
  have hwv : w v = f := sub_eq_zero.mp ((hPf _).symm.trans hmem)
  have hv (x : G) : v (d x) = f x := by
    have hh := hw v 1 (d x)
    change w v (1 * d.symm (d x)) = _ at hh
    simpa [hwv] using hh.symm
  let I : Set ℝ := {0}
  let idm := ContinuousMonoidHom.id ℝ≥0ˣ
  let u : ModulatedExponentialDecay idm I := ⟨v.val, by
    change v.val ∈ modulatedExponentialDecaySubmodule idm {0}
    rw [modulatedExponentialDecaySubmodule_singleton_zero]
    exact v.property⟩
  obtain ⟨L,hL⟩ := identityModulationExponentialDecay_equiv I (ordConnected_singleton)
    (singleton_nonempty 0)
  let z := L.symm u
  let a : I := ⟨0, rfl⟩
  refine ⟨logExponentialDecayTwist I a z, fun x ↦ ?_⟩
  refine (logExponentialDecayTwist_apply I a z _).trans ?_
  change (Real.exp (0 * _) : ℂ) * z.val _ = _
  simp only [zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
  exact (hL z (d x)).symm.trans ((congrArg (fun t : ModulatedExponentialDecay idm I ↦ t.val (d x))
    (L.apply_symm_apply u)).trans (hv x))

/-- The character-weighted coset integral is smooth on the logarithmic norm line. -/
private theorem spectralNuclearity_trace_coset_profile (χ : PontryaginDual C𝔽) (φ : 𝒟) :
    ∃ b : 𝓢(ℝ, ℂ), ∀ x : ℝ, b x = ∫ h : C₁,
      (χ (σ₀(x) * h.val) : ℂ) * φ.val (σ₀(x) * h.val)
        ∂normOneIdeleClassTamagawaMeasure F := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let c : ℝ≥0ˣ → C𝔽 := fun u ↦ QuotientGroup.mk (canonicalIdeleNormSection F u)
  have hc : Continuous c :=
    QuotientGroup.continuous_mk.comp (canonicalIdeleNormSection_continuous F)
  have hcr : RightInverse c (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let e : (C𝔽 ⧸ C₁) ≃ₜ* ℝ≥0ˣ :=
    { QuotientGroup.quotientKerEquivOfRightInverse (ideleClassNorm F) c hcr with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (isProperMap_ideleClassNorm F).continuous
      continuous_invFun := QuotientGroup.continuous_mk.comp hc }
  let f₀ : SchwartzBruhat C𝔽 := ⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩
  obtain ⟨proj, hP⟩ := schwartzBruhat_mul_unitaryCharacter χ
  have hK : IsCompact (C₁ : Set C𝔽) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage isCompact_singleton
  let : LocallyCompactSpace C₁ := hK.isClosed.locallyCompactSpace
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : (normOneIdeleClassTamagawaMeasure F).Regular :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.2.1
  let f₁ := schwartzBruhatCosetIntegral C₁ (normOneIdeleClassTamagawaMeasure F) hK.isClosed (proj f₀)
  let : CommGroup (C𝔽 ⧸ C₁) := QuotientGroup.Quotient.commGroup C₁
  let : T2Space (C𝔽 ⧸ C₁) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (C𝔽 ⧸ C₁) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  obtain ⟨b, hb⟩ := spectralNuclearity_trace_schwartz_log e f₁
  refine ⟨b, fun x ↦ ?_⟩
  let q : C𝔽 ⧸ C₁ := QuotientGroup.mk (σ₀(x))
  have hq : Real.log ((e q).val : ℝ) = x := by
    change Real.log ((ideleClassNorm F (σ₀(x))).val : ℝ) = x
    rw [spectralNuclearity_trace_section_norm, Units.val_mk0, Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
  calc
      b x = f₁ q := (congrArg b hq.symm).trans (hb q)
      _ = ∫ h : C₁, (proj f₀) (σ₀(x) * h.val) ∂normOneIdeleClassTamagawaMeasure F :=
        schwartzBruhatCosetIntegral_mk C₁ (normOneIdeleClassTamagawaMeasure F) hK.isClosed (proj f₀) _
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with h
        exact hP f₀ (σ₀(x) * h.val)

/-- Disintegrate idèle-class Tamagawa measure over the norm-one classes and the real logarithmic
norm. -/
private theorem spectralNuclearity_trace_integral_log_norm (σ : ℝ≥0ˣ → C𝔽) (hσ : Continuous σ)
    (hσnorm : RightInverse σ (ideleClassNorm F)) (f : C𝔽 → ℂ)
    (hfc : Continuous f) (hf : Integrable f (ideleClassTamagawaMeasure F)) :
    (∫ g, f g ∂ideleClassTamagawaMeasure F) = ∫ y : ℝ,
      ∫ h : C₁, f (σ (Units.mk0 (Real.exp y).toNNReal (by positivity)) * h.val)
        ∂normOneIdeleClassTamagawaMeasure F := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : MeasurableSpace (C𝔽 ⧸ C₁) := borel _
  let : BorelSpace (C𝔽 ⧸ C₁) := ⟨rfl⟩
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let d : C𝔽 ⧸ C₁ ≃ₜ* ℝ≥0ˣ :=
    { QuotientGroup.quotientKerEquivOfRightInverse (ideleClassNorm F) σ hσnorm with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (isProperMap_ideleClassNorm F).continuous
      continuous_invFun := QuotientGroup.continuous_mk.comp hσ }
  let D := d.toHomeomorph.toMeasurableEquiv
  let ν := positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))
  have hν : positiveRealHaar.map D.symm = ν := D.map_symm
  have hWeil := normOneIdeleClassTamagawaMeasure_isWeil F
  have havg := weilQuotientIntegral_L1 C₁
    (isClosed_singleton.preimage (isProperMap_ideleClassNorm F).continuous)
    (ideleClassTamagawaMeasure F) (normOneIdeleClassTamagawaMeasure F) ν hWeil hf
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have he (y : ℝ) : e y = Units.mk0 (Real.exp y).toNNReal (by positivity) :=
    Units.ext (NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos y).le).symm)
  have hE : positiveRealHaar = volume.map e := by
    unfold positiveRealHaar
    congr 1
    exact funext fun y ↦ (he y).symm
  rw [havg.2.2, ← hν, integral_map_equiv, hE]
  change (∫ t, lcaCosetIntegral C₁ (normOneIdeleClassTamagawaMeasure F) f (D.symm t)
    ∂volume.map e) = _
  rw [show (⇑e) = ⇑e.toMeasurableEquiv from rfl, integral_map_equiv]
  apply integral_congr_ae
  filter_upwards with y
  change lcaCosetIntegral C₁ _ f (D.symm (e y)) = _
  rw [he]
  change lcaCosetIntegral C₁ _ f (QuotientGroup.mk (σ _)) = _
  apply lcaCosetIntegral_mk
  exact (hfc.comp (continuous_const.mul continuous_subtype_val)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The test Mellin transform is the ordinary Mellin transform of a compactly supported smooth
logarithmic profile. -/
private theorem spectralNuclearity_trace_mellin_profile (χ : PontryaginDual C𝔽) (φ : 𝒟) :
    ∃ b : 𝓢(ℝ, ℂ), HasCompactSupport (b : ℝ → ℂ) ∧ ∀ s : ℂ,
      nuclearityTestMellin χ φ s = mellin (fun t : ℝ ↦ b (Real.log t)) s := by
  obtain ⟨b, hb⟩ := spectralNuclearity_trace_coset_profile χ φ
  let L (g : C𝔽) := Real.log ((ideleClassNorm F g).val : ℝ)
  have hL : Continuous L :=
    Real.continuousOn_log.comp_continuous (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous))
      fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hK : IsCompact (L '' tsupport φ.val) := φ.property.2.image hL
  have hbc : HasCompactSupport (b : ℝ → ℂ) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro t ht
    by_contra hno
    apply ht
    rw [hb]
    apply integral_eq_zero_of_ae
    filter_upwards with g
    have ht' : σ₀(t) * g.val ∉ tsupport φ.val := fun hsup ↦
      hno ⟨_, hsup, by dsimp [L]; rw [spectralNuclearity_trace_coset_norm, Real.log_exp]⟩
    simp only [image_eq_zero_of_notMem_tsupport ht', mul_zero, Pi.zero_apply]
  refine ⟨b, hbc, fun s ↦ ?_⟩
  let σ : ℝ≥0ˣ → C𝔽 := fun u ↦ QuotientGroup.mk (canonicalIdeleNormSection F u)
  have hσ : Continuous σ := QuotientGroup.continuous_mk.comp (canonicalIdeleNormSection_continuous F)
  have hφ : Continuous φ.val :=
    schwartzBruhat_continuous (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  refine (spectralNuclearity_trace_integral_log_norm σ hσ (canonicalIdeleNormSection_rightInverse F)
    (fun g ↦ φ.val g * ideleClassNormTwist χ s g) (hφ.mul (ideleClassNormTwist χ s).continuous)
    ((nuclearityTestMellin_integrable χ φ).1 s)).trans ?_
  rw [mellin, ← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards with y
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [hb, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with g
  let w := σ₀(y) * g.val
  change φ.val w * ((χ w : ℂ) * (((ideleClassNorm F w).val : ℝ) : ℂ) ^ s) = _
  rw [show ((ideleClassNorm F w).val : ℝ) = Real.exp y from spectralNuclearity_trace_coset_norm y g]
  have hp : (Real.exp y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos y).ne'
  rw [Complex.cpow_sub _ _ hp, Complex.cpow_one]
  dsimp [w]
  field_simp

/-- On each bounded vertical strip the Mellin transform of a compactly supported test decays
faster than any fixed inverse power of the height. -/
private theorem spectralNuclearity_trace_vertical_decay (χ : PontryaginDual C𝔽) (φ : 𝒟) (a b : ℝ)
    (hab : a < b) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C > (0 : ℝ), ∀ᶠ y : ℝ in comap abs atTop, ∀ σ ∈ Icc a b,
      ‖nuclearityTestMellin χ φ ((σ : ℂ) + y * Complex.I)‖ ≤ C / |y| ^ k := by
  obtain ⟨f, hs, hf⟩ := spectralNuclearity_trace_mellin_profile χ φ
  have hwt (r : ℝ) (_ : r ∈ Icc a b) : ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = (Real.exp (r * x) : ℂ) * f x := by
    let v := fun x : ℝ ↦ (Real.exp (r * x) : ℂ) * f x
    have hv : ContDiff (ℝ) (∞) v :=
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))).mul
        (f.smooth _)
    have hvc : HasCompactSupport v := hs.mul_left
    exact ⟨hvc.toSchwartzMap hv, fun _ ↦ rfl⟩
  simpa only [hf] using mellin_eventualHeightBound_of_weighted_schwartz f a b hab hwt k hk

/-- A summable weighted zero count dominates functions that decay quadratically outside bounded
height. -/
private theorem spectralNuclearity_trace_summable_of_decay {ι : Type*} (y m : ι → ℝ)
    (hm : ∀ i, 1 ≤ m i) (hmw : Summable (fun i ↦ m i / (1 + |y i|) ^ 2))
    (f : ι → ℂ) (C : ℝ) (hC : 0 < C)
    (hf : ∀ᶠ t : ℝ in comap abs atTop, ∀ i, y i = t → ‖f i‖ ≤ C / |t| ^ 2) :
    Summable (fun i ↦ m i * ‖f i‖) := by
  have hy : Tendsto (fun i ↦ |y i|) cofinite atTop := by
    apply tendsto_atTop.2
    intro T
    let R := max T 1
    have hp : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
    have he : 0 < 1 / (1 + R) ^ 2 := by positivity
    filter_upwards [hmw.tendsto_cofinite_zero.eventually_lt_const he] with i hi
    by_contra! h
    have hlt : |y i| < R := lt_of_lt_of_le h (le_max_left _ _)
    have hle : (1 + |y i|) ^ 2 ≤ (1 + R) ^ 2 := by gcongr
    have hh := div_le_div_of_nonneg_left (zero_le_one : (0 : ℝ) ≤ 1) (by positivity : 0 < (1 + |y i|) ^ 2) hle
    exact (not_lt_of_ge (hh.trans (div_le_div_of_nonneg_right (hm i) (by positivity)))) hi
  have hfreq : Tendsto y cofinite (comap abs atTop) := tendsto_comap_iff.mpr hy
  refine (hmw.mul_left (4 * C)).of_norm_bounded_eventually ?_
  filter_upwards [hfreq.eventually hf, hy.eventually_ge_atTop 1] with i hi hi1
  rw [Real.norm_of_nonneg (mul_nonneg (zero_le_one.trans (hm i)) (norm_nonneg _))]
  have hp : 0 < |y i| := zero_lt_one.trans_le hi1
  have hsq : (1 + |y i|) ^ 2 ≤ 4 * |y i| ^ 2 := by nlinarith
  have hdom : C / |y i| ^ 2 ≤ (4 * C) / (1 + |y i|) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq hC.le]
  calc _ ≤ m i * ((4 * C) / (1 + |y i|) ^ 2) :=
           mul_le_mul_of_nonneg_left ((hi i rfl).trans hdom) (zero_le_one.trans (hm i))
       _ = _ := by ring

local notation "right(" a ")" => (Complex.re ⁻¹' Ioi (a : ℝ))
local notation "zeroOrder(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "windowZeros(" χ ", " d ")" =>
  {s : ℂ // 0 < zeroOrder(χ, s) ∧ |s.re - 1 / 2| < (d : ℝ)}
/-- Removing the gamma factor gives a continuation of the finite L-function. The entire
reciprocal gamma factor can only increase the order at a zero. -/
private theorem spectralNuclearity_trace_finite_companion (χ : U) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧ (∀ z : right(1), L z = finiteHeckeL χ z) ∧
      ∀ z, meromorphicOrderAt (continuedCompletedHeckeL χ) z ≤ meromorphicOrderAt L z := by
  let Λ := continuedCompletedHeckeL χ
  let G (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  let product := G * Λ
  obtain ⟨hΛ, hval⟩ := continuedCompletedHeckeL_spec χ
  have hG := differentiable_inv_heckeGammaFactor χ
  have hm : MeromorphicOn product univ := fun z hz ↦
    (hG.analyticAt z).meromorphicAt.mul (hΛ hz).meromorphicAt
  refine ⟨toMeromorphicNFOn product univ, meromorphicNFOn_toMeromorphicNFOn _ _, ?_, ?_⟩
  · intro z
    have hγ := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans z.property)
    have hNF : MeromorphicNFAt product z :=
      (meromorphicNFAt_mul_iff_right (hG.analyticAt z) (inv_ne_zero hγ)).2 (hΛ (mem_univ _))
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _), toMeromorphicNFAt_eq_self.mpr hNF]
    simp [product, Λ, G, hval z, completedHeckeL, finiteHeckeL, hγ]
  · intro z
    rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ _),
      show meromorphicOrderAt product z = _ from meromorphicOrderAt_mul
        (hG.analyticAt z).meromorphicAt (hΛ (mem_univ z)).meromorphicAt]
    exact le_add_of_nonneg_left (hG.analyticAt z).meromorphicOrderAt_nonneg

/-- Zeros in a vertical strip, counted with multiplicity, have a summable quadratic weight. -/
private theorem spectralNuclearity_trace_zero_count (χ : U) (a : ℝ) :
    Summable (fun r : windowZeros(χ, a) ↦ (zeroOrder(χ, r.val) : ℝ) / (1 + |r.val.im|) ^ 2) := by
  obtain ⟨L, hL, hSeries, hOrder⟩ := spectralNuclearity_trace_finite_companion χ
  obtain ⟨hLine, k, _, hInv⟩ := finiteHeckeL_inv_isBigO_oneLine χ L hL hSeries
  exact summable_divisor_div_one_add_abs_im_sq (k := k) (σ := 1)
    (continuedCompletedHeckeL_spec χ).1.meromorphicOn hL hOrder
    (finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries) (hLine.mono fun _ ht ↦ ht.2)
    hInv (1 / 2) a

private theorem spectralNuclearity_trace_zero_re_lt_one (χ : PontryaginDual C𝔽) {z : ℂ}
    (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) z) : z.re < 1 := by
  rcases le_or_gt z.re 0 with h | h
  · exact h.trans_lt zero_lt_one
  · obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec χ
    exact completedHeckeL_continuation_zeros χ _ hL heq h hz

private theorem spectralNuclearity_trace_zero_strip (χ : U) {z : ℂ} (hz : 0 < zeroOrder(χ, z)) :
    0 < z.re ∧ z.re < 1 := by
  obtain ⟨hL, hLh⟩ := continuedCompletedHeckeL_spec χ
  have hp : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) z := by
    rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)] at hz
    cases he : meromorphicOrderAt (continuedCompletedHeckeL χ) z with
    | top => simp
    | coe k =>
      rw [he, WithTop.untop₀_coe] at hz
      exact_mod_cast hz
  have hu := spectralNuclearity_trace_zero_re_lt_one χ hp
  obtain ⟨hD, hDh⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε, hε, hne, hfe⟩ :=
    completedHeckeL_continuation_functionalEquation χ _ _ hL hLh hD hDh
  have hcomp : meromorphicOrderAt (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) z =
      meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) (1 - z) := by
    simpa [Function.comp_def] using
      meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹)
        (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) z by fun_prop)
        (show deriv (fun s : ℂ ↦ 1 - s) z ≠ 0 by simp)
  rw [show (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) =
      ε * continuedCompletedHeckeL χ from funext hfe,
    meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z) (hne z)] at hcomp
  have hl := spectralNuclearity_trace_zero_re_lt_one χ⁻¹ (hcomp ▸ hp)
  rw [Complex.sub_re, Complex.one_re] at hl
  exact ⟨by linarith, hu⟩

/-- The trace terms for the untruncated divisor are absolutely summable throughout the shifted
critical strip. -/
private theorem spectralNuclearity_trace_divisor_summable (χ : U) (φ : 𝒟) (a : ℝ) :
    Summable (fun z : {s : ℂ // 0 < zeroOrder(χ, s)} ↦
      ‖(zeroOrder(χ, z.val) : ℂ) * nuclearityTestMellin χ φ (z.val - (a : ℂ))‖) := by
  let Z := {s : ℂ // 0 < zeroOrder(χ, s)}
  have hstrip (z : Z) : 0 < z.val.re ∧ z.val.re < 1 := spectralNuclearity_trace_zero_strip χ z.property
  let e (z : Z) : windowZeros(χ, 1) := ⟨z.val, z.property, by
    obtain ⟨hl, hu⟩ := hstrip z
    exact abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  have he : Injective e := fun _ _ h ↦ Subtype.ext (congrArg (fun r : windowZeros(χ, 1) ↦ r.val) h)
  have hs := (spectralNuclearity_trace_zero_count χ 1).comp_injective he
  have hm (z : Z) : 1 ≤ (zeroOrder(χ, z.val) : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ zeroOrder(χ, z.val) from z.property)
  obtain ⟨C, hC, hf⟩ := spectralNuclearity_trace_vertical_decay χ φ (-a) (1 - a) (by linarith) 2 (by decide)
  have H := spectralNuclearity_trace_summable_of_decay (ι := Z) (fun z ↦ z.val.im)
    (fun z ↦ (zeroOrder(χ, z.val) : ℝ)) hm hs
    (fun z ↦ nuclearityTestMellin χ φ (z.val - (a : ℂ))) C hC (by
      filter_upwards [hf] with t ht z heq
      have hre := hstrip z
      have hb : (z.val - (a : ℂ)).re ∈ Icc (-a) (1 - a) := by
        simp only [Complex.sub_re, Complex.ofReal_re, mem_Icc]
        constructor <;> linarith [hre.1, hre.2]
      have hh := ht _ hb
      have him : (z.val - (a : ℂ)).im = t := by simpa using heq
      rwa [← him, Complex.re_add_im, him] at hh)
  apply H.congr
  intro z
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg (zero_le_one.trans (hm z))]

/-- At a zero of the regularized completed function, its finite analytic multiplicity is exactly
the order in the original divisor. -/
private theorem spectralNuclearity_trace_zero_order (χ : U) (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F)
    (hτ : RightInverse τ (ideleNorm F)) (z : zeros(χ, τ, hτ)) :
    ∃ k : ℕ, 0 < k ∧ analyticOrderAt ((Λ(χ, τ, hτ)).val : ℂ → ℂ) z.val = k ∧
      zeroOrder(χ, z.val) = k := by
  classical
  let G := Λ(χ, τ, hτ)
  let L := continuedCompletedHeckeL χ
  obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec χ
  let x := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let b := (x : ℂ) * Complex.I
  let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
  let product (s : ℂ) := (s + b) ^ δ * (1 - s - b) ^ δ
  have hA : AnalyticAt ℂ (G.val : ℂ → ℂ) z.val := G.property.analyticAt _
  have hP (s : ℂ) : AnalyticAt ℂ product s := by
    dsimp only [product]
    fun_prop
  have hG0 : G.val z.val = 0 := hA.analyticOrderAt_ne_zero.mp z.property.ne'
  have hP0 : product z.val ≠ 0 := by
    by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · obtain ⟨h₀, h₁⟩ := regularizedCompletedHeckeL_ne_zero_at_canceled_poles χ τ hτ L hL heq hχ
      have hn₀ : z.val ≠ -b := fun e ↦ h₀ (e ▸ hG0)
      have hn₁ : z.val ≠ 1 - b := fun e ↦ h₁ (e ▸ hG0)
      have hsum : z.val + b ≠ 0 := fun e ↦ hn₀ (by linear_combination e)
      have hdiff : 1 - z.val - b ≠ 0 := fun e ↦ hn₁ (by linear_combination -e)
      simpa [product, δ, hχ] using mul_ne_zero hsum hdiff
    · simp [product, δ, hχ]
  have hmer : MeromorphicOn (product * L) univ := fun s hs ↦
    (hP s).meromorphicAt.mul (hL hs).meromorphicAt
  have horder : meromorphicOrderAt (G.val : ℂ → ℂ) z.val = meromorphicOrderAt L z.val := by
    change meromorphicOrderAt (toMeromorphicNFOn (product * L) univ) z.val = _
    rw [meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ _),
      meromorphicOrderAt_mul (hP _).meromorphicAt (hL (mem_univ _)).meromorphicAt,
      (hP _).meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hP0)]
    simp [L]
  have htwo : meromorphicOrderAt L 2 ≠ ⊤ := by
    intro h
    have hp : 0 < meromorphicOrderAt L 2 := h ▸ WithTop.coe_lt_top (0 : ℤ)
    have hb := completedHeckeL_continuation_zeros χ _ hL heq (by norm_num : 0 < (2 : ℂ).re) hp
    norm_num at hb
  have hfin := hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ z.val) htwo
  rw [hA.meromorphicOrderAt_eq] at horder
  have hne : analyticOrderAt (G.val : ℂ → ℂ) z.val ≠ ⊤ := by
    intro h
    rw [h] at horder
    exact hfin horder.symm
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  have hz := z.property
  change 0 < analyticOrderAt (G.val : ℂ → ℂ) z.val at hz
  rw [← hk] at hz horder
  refine ⟨k, by exact_mod_cast hz, hk.symm, ?_⟩
  rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _), ← horder]
  simp

private theorem spectralNuclearity_trace_term_summable (χ : U) (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F)
    (hτ : RightInverse τ (ideleNorm F)) (a : ℝ) (N : ℕ) (φ : 𝒟) :
    Summable (fun z : zeros(χ, τ, hτ) ↦
      ‖((min N (analyticOrderAt ((Λ(χ, τ, hτ)).val : ℂ → ℂ) z.val).toNat : ℕ) : ℂ) *
        nuclearityTestMellin χ φ (z.val - (a : ℂ))‖) := by
  classical
  let ι (z : zeros(χ, τ, hτ)) : {s : ℂ // 0 < zeroOrder(χ, s)} :=
    ⟨z.val, by
      obtain ⟨k, hk, _, he⟩ := spectralNuclearity_trace_zero_order χ τ hτ z
      rw [he]
      exact_mod_cast hk⟩
  have hinj : Injective ι := fun _ _ e ↦ Subtype.ext (congrArg (fun r : {s : ℂ // 0 < zeroOrder(χ, s)} ↦ r.val) e)
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _
    ((spectralNuclearity_trace_divisor_summable χ φ a).comp_injective hinj)
  intro z
  obtain ⟨k, _, hord, hdiv⟩ := spectralNuclearity_trace_zero_order χ τ hτ z
  change _ ≤ ‖(zeroOrder(χ, z.val) : ℂ) * nuclearityTestMellin χ φ (z.val - (a : ℂ))‖
  rw [hord, hdiv, ENat.toNat_natCast, Int.cast_natCast, norm_mul, norm_mul,
    Complex.norm_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.min_le_right N k) (norm_nonneg _)

end SpectralTraceEstimates

open Classical in
/-- By the Leibniz rule, vanishing of the retained jets is invariant under Mellin multiplication.
The action therefore descends through both quotients. -/
private theorem spectralNuclearity_trace_descends (a : ℝ) (N : ℕ) (φ : 𝒟)
    (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a)))
    (hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ)))
    (A : B →L[ℂ] B) (hA : ∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s)
    (hD : Set.MapsTo A (D(a) : Set B) (D(a))) :
    let K := ⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker
    let E := Q(a) ⧸ K
    ∃ (Aq : Q(a) →L[ℂ] Q(a)) (T : E →L[ℂ] E),
      (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) ∧
      ∀ x, T (K.mkQ x) = K.mkQ (Aq x) := by
  intro K E
  let S := (D(a)).mapQ (D(a)) A.toLinearMap fun x hx ↦ hD hx
  let Aq : Q(a) →L[ℂ] Q(a) := ⟨S, (Submodule.isQuotientMap_mkQ (D(a))).continuous_iff.mpr
    ((Submodule.isQuotientMap_mkQ (D(a))).continuous.comp A.continuous)⟩
  have hAq (f : B) : Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f) := rfl
  have hK (x : Q(a)) (hx : x ∈ K) : Aq x ∈ K := by
    obtain ⟨f, rfl⟩ := (D(a)).mkQ_surjective x
    rw [Submodule.mem_iInf] at hx ⊢
    intro i
    change d i.val (Aq ((D(a)).mkQ f)) = 0
    rw [hAq, hd]
    have hf : Differentiable ℂ f.val := fun z ↦
      (f.property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    have hprod : (A f).val = nuclearityTestMellin χ φ * f.val := funext (hA f)
    rw [hprod, iteratedDeriv_mul
      (archNuclearityDenominator_closed_invariant_multiplier χ φ).contDiff.contDiffAt
      hf.contDiff.contDiffAt]
    apply Finset.sum_eq_zero
    intro k _
    let j : jets(χ, τ, hτ) := ⟨i.val.1, i.val.2.val - k, (Nat.sub_le _ _).trans_lt i.val.2.isLt⟩
    have hzero : d j ((D(a)).mkQ f) = 0 :=
      hx ⟨j, (Nat.sub_le _ _).trans_lt i.property⟩
    rw [hd] at hzero
    exact mul_eq_zero_of_right _ hzero
  let T₀ := K.mapQ K Aq.toLinearMap hK
  let T : E →L[ℂ] E := ⟨T₀, (Submodule.isQuotientMap_mkQ K).continuous_iff.mpr
    ((Submodule.isQuotientMap_mkQ K).continuous.comp Aq.continuous)⟩
  exact ⟨Aq, T, hAq, fun _ ↦ rfl⟩

-- TODO(paper-gap): The proof on p. 367 gives no uniform boundedness estimate for
-- the rescaled biorthogonal vectors. Discreteness does not control zero counts,
-- enumeration order, or separation. It also does not imply N(z)! = O(|Im z|).

/-- The entire Schwartz–Bergman space is nuclear through the Fourier–Mellin equivalence. -/
private theorem spectralJet_sb_nuclear :
    IsNuclearTVS.{0} (SchwartzBergman (univ : Set ℝ)) := by
  let : PolynormableSpace ℂ (SchwartzBergman (univ : Set ℝ)) :=
    (schwartzBergman_frechet univ isOpen_univ ordConnected_univ univ_nonempty).choose_spec.1
  exact nuclear_of_equiv
    (positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty)
    (positiveRealExponentialDecay_nuclear univ ordConnected_univ univ_nonempty)

/-- In the actual retained quotient all nuclear presentations give the same trace. -/
private theorem spectralJet_unique_presentation_sum (a : ℝ) (N : ℕ) (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a))) :
    let Q := Q(a)
    let K := ⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker
    let E := Q ⧸ K
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    ∀ T : E →L[ℂ] E, Nonempty (NuclearPresentation T) → ∃! t : ℂ, ∀ r : NuclearPresentation T,
      Summable (fun n ↦ ‖r.coeff n * r.functional n (r.vector n).val‖) ∧
      HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) t := by
  intro Q K E T hr
  let D := D(a)
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsClosed (D : Set B) := schwartzBergmanDivisible_isClosed _
  have hB : IsNuclearTVS.{0} B := spectralJet_sb_nuclear
  let : T2Space B := hB.1
  let : PolynormableSpace ℂ B := hB.2.1
  let : T2Space Q := inferInstanceAs (T2Space (B ⧸ D))
  have hQ : IsNuclearTVS.{0} Q := isNuclearTVS_quotient hB D
  let : PolynormableSpace ℂ Q := hQ.2.1
  let : IsClosed (K : Set Q) := by
    change IsClosed (↑(⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker) : Set Q)
    rw [Submodule.coe_iInf]
    exact isClosed_iInter (fun i ↦ (d i.val).isClosed_ker)
  let : T2Space E := inferInstanceAs (T2Space (Q ⧸ K))
  have hE : IsNuclearTVS.{0} E := isNuclearTVS_quotient hQ K
  let : PolynormableSpace ℂ E := hE.2.1
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have hAP := dense_finiteRank_of_isNuclearTVS E hE
  exact exists_nuclearTrace_hasSum hAP T ((isNuclearOperator_iff_nonempty_presentation T).mpr hr)

open Classical in
/-- Paper: Theorem 7.4.1.1(2), pp. 366–367. Every finite set of zero sites has a
unique continuous projector onto its retained jets. Its range is finite dimensional
and invariant under the multiplier, whose restriction has the finite divisor trace. -/
private theorem spectralNuclearity_trace_finite_cluster (a : ℝ) (N : ℕ) (φ : 𝒟)
    (d : jets(χ,τ,hτ) → StrongDual ℂ (Q(a)))
    (hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val-(a:ℂ))) :
    let Q := Q(a)
    let I := {i : jets(χ,τ,hτ) // i.2.val < N}
    let K := ⨅ i : I, (d i.val).toLinearMap.ker
    let E := Q ⧸ K
    ∀ (A : B →L[ℂ] B) (Aq : Q →L[ℂ] Q) (T : E →L[ℂ] E),
      (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) →
      (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) →
      (∀ x, T (K.mkQ x) = K.mkQ (Aq x)) →
      ∀ (L : I → StrongDual ℂ E), (∀ i x, L i (K.mkQ x) = d i.val x) →
      ∀ C : Finset (zeros(χ,τ,hτ)), ∃ proj : E →L[ℂ] E,
        (∀ i x, L i (proj x) = if i.val.1 ∈ C then L i x else 0) ∧
        (∀ x, proj (proj x) = proj x) ∧ (∀ x, T (proj x) = proj (T x)) ∧
        FiniteDimensional ℂ proj.toLinearMap.range ∧
        (∃ T' : proj.toLinearMap.range →ₗ[ℂ] proj.toLinearMap.range,
          (∀ x, (T' x).val = T x.val) ∧ LinearMap.trace ℂ _ T' =
            ∑ z ∈ C, ((min N (multiplicity(χ,τ,hτ,z)) : ℕ):ℂ) * nuclearityTestMellin χ φ (z.val-(a:ℂ))) ∧
        ∀ R : E →L[ℂ] E, (∀ i x, L i (R x) = if i.val.1 ∈ C then L i x else 0) → R=proj := by
  classical
  intro Q I K E A Aq T hA hAq hT L hL C
  let n (z : zeros(χ,τ,hτ)) := min N (multiplicity(χ,τ,hτ,z))
  let t (i : I) : Fin (n i.val.1) := ⟨i.val.2.val,lt_min i.property i.val.2.isLt⟩
  let idx (z : zeros(χ,τ,hτ)) (j : Fin (n z)) : I :=
    ⟨⟨z,j.val,j.isLt.trans_le (min_le_right N _)⟩,j.isLt.trans_le (min_le_left N _)⟩
  choose f hf using exists_spectralNuclearityBiorthogonal_vectors χ τ hτ a
  let b (i : I) : E := K.mkQ ((D(a)).mkQ (f i.val))
  have bio (i j : I) : L i (b j) = if i=j then 1 else 0 := by
    change L i (K.mkQ ((D(a)).mkQ _)) = _
    rw [hL,hd,hf]
    simp only [Subtype.val_inj]
  have sep : Injective (fun x : E ↦ fun i : I ↦ L i x) := by
    intro x y h
    apply sub_eq_zero.mp
    obtain ⟨v,hv⟩ := K.mkQ_surjective (x-y)
    rw [←hv,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,Submodule.mem_iInf]
    intro i
    change d i.val v = 0
    rw [←hL,hv,map_sub,sub_eq_zero]
    exact congrFun h i
  let S := C.biUnion fun z ↦ Finset.univ.image (idx z)
  have memS (i : I) : i ∈ S ↔ i.val.1 ∈ C := by
    constructor
    · intro h
      obtain ⟨z,hz,hj⟩ := Finset.mem_biUnion.mp h
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hj
      exact hz
    · intro h
      exact Finset.mem_biUnion.mpr ⟨i.val.1,h,Finset.mem_image.mpr ⟨t i,Finset.mem_univ _,rfl⟩⟩
  let proj : E →L[ℂ] E := ∑ j ∈ S, (L j).smulRight (b j)
  have valP (x : E) : proj x = ∑ j ∈ S, L j x • b j := by
    simp [proj]
  have hp (i : I) (x : E) : L i (proj x) = if i.val.1 ∈ C then L i x else 0 := by
    rw [valP,map_sum]
    simp only [map_smul,bio,smul_eq_mul,mul_ite,mul_one,mul_zero]
    simp [Finset.sum_ite_eq,memS]
  let lower (i : I) (k : ℕ) : I :=
    ⟨⟨i.val.1,i.val.2.val-k,(Nat.sub_le _ _).trans_lt i.val.2.isLt⟩,(Nat.sub_le _ _).trans_lt i.property⟩
  have row (i : I) (x : E) : L i (T x) = ∑ k ∈ Finset.range (i.val.2.val+1),
      (i.val.2.val.choose k : ℂ) * iteratedDeriv k (nuclearityTestMellin χ φ) (i.val.1.val-(a:ℂ)) * L (lower i k) x := by
    obtain ⟨y,rfl⟩ := K.mkQ_surjective x
    obtain ⟨f,rfl⟩ := (D(a)).mkQ_surjective y
    rw [hT,hAq,hL,hd,show (A f).val = nuclearityTestMellin χ φ * f.val from funext (hA f)]
    have hf : Differentiable ℂ f.val := fun z ↦
      (f.property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    rw [iteratedDeriv_mul (archNuclearityDenominator_closed_invariant_multiplier χ φ).contDiff.contDiffAt
      hf.contDiff.contDiffAt]
    apply Finset.sum_congr rfl
    intro k _
    rw [hL,hd]
  have idem : ∀ x, proj (proj x) = proj x := by
    intro x
    apply sep
    funext i
    change L i (proj (proj x)) = L i (proj x)
    by_cases h : i.val.1 ∈ C <;> simp [hp,h]
  have comm : ∀ x, T (proj x) = proj (T x) := by
    intro x
    apply sep
    funext i
    change L i (T (proj x)) = L i (proj (T x))
    rw [row i (proj x),hp i (T x),row i x]
    by_cases h : i.val.1 ∈ C <;> simp [hp,lower,h]
  have finite : FiniteDimensional ℂ proj.toLinearMap.range := by
    let rangeSpace := Submodule.span ℂ (b '' (S : Set I))
    let : FiniteDimensional ℂ rangeSpace := FiniteDimensional.span_of_finite ℂ (S.finite_toSet.image b)
    have hsub : proj.toLinearMap.range ≤ rangeSpace := by
      rintro _ ⟨x,rfl⟩
      change proj x ∈ rangeSpace
      rw [valP]
      exact Submodule.sum_mem rangeSpace fun i hi ↦ rangeSpace.smul_mem _ (Submodule.subset_span ⟨i,hi,rfl⟩)
    exact FiniteDimensional.of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)
  refine ⟨proj,hp,idem,comm,finite,?_,?_⟩
  · let rangeSpace := proj.toLinearMap.range
    let : FiniteDimensional ℂ rangeSpace := finite
    let ℓ (i : I) : rangeSpace →ₗ[ℂ] ℂ := (L i).toLinearMap.comp rangeSpace.subtype
    let y (i : I) : rangeSpace := ⟨proj (T (b i)),⟨_,rfl⟩⟩
    let R : rangeSpace →ₗ[ℂ] rangeSpace := ∑ i ∈ S, (ℓ i).smulRight (y i)
    have pfix (x : rangeSpace) : proj x.val = x.val := by
      obtain ⟨u,hu⟩ := x.property
      change proj u = x.val at hu
      rw [←hu,idem]
    refine ⟨R,?_,?_⟩
    · intro x
      calc
        (R x).val = ∑ i ∈ S, L i x.val • proj (T (b i)) := by
          change rangeSpace.subtype (R x) = _
          simp only [R,LinearMap.sum_apply,map_sum,LinearMap.smulRight_apply,map_smul]
          rfl
        _ = proj (T (proj x.val)) := by rw [valP x.val,map_sum,map_sum]; simp only [map_smul]
        _ = T x.val := by rw [←comm,idem,pfix]
    · have diag (i : I) : L i (T (b i)) = nuclearityTestMellin χ φ (i.val.1.val-(a:ℂ)) := by
        rw [row,Finset.sum_eq_single 0]
        · have e0 : lower i 0 = i := by rfl
          rw [e0,bio,ite_eq_left rfl]
          simp
        · intro j hj hj0
          have hn : lower i j ≠ i := by
            intro he
            have eqv : i.val.2.val-j = i.val.2.val := congrArg (fun k : I ↦ k.val.2.val) he
            have hle := Finset.mem_range.mp hj
            omega
          rw [bio,ite_eq_right hn,mul_zero]
        · simp
      have dis : (C : Set _).PairwiseDisjoint (fun z ↦ Finset.univ.image (idx z)) := by
        intro z _ w _ hzw
        apply Finset.disjoint_left.mpr
        intro i hi hi'
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨k,_,h⟩ := Finset.mem_image.mp hi'
        exact hzw (congrArg (fun x : I ↦ x.val.1) h).symm
      calc
        LinearMap.trace ℂ rangeSpace R = ∑ i ∈ S, ℓ i (y i) := by simp only [R,map_sum,LinearMap.trace_smulRight]
        _ = ∑ i ∈ S, nuclearityTestMellin χ φ (i.val.1.val-(a:ℂ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          change L i (proj (T (b i))) = _
          rw [hp,ite_eq_left ((memS i).mp hi),diag]
        _ = _ := by
          rw [show S = C.biUnion (fun z ↦ Finset.univ.image (idx z)) from rfl, Finset.sum_biUnion dis]
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.sum_image (fun j _ k _ he ↦ Fin.ext (congrArg (fun u : I ↦ u.val.2.val) he))]
          simp [idx,n,nsmul_eq_mul]
  · intro R hR
    ext x
    apply sep
    funext i
    change L i (R x) = L i (proj x)
    rw [hR,hp]

section SpectralTraceHilbert

open Filter
open scoped InnerProductSpace

/-- The inclusion of the complete gauge space of a Banach disc into the ambient space is continuous. -/
private theorem spectralTrace_banachDisc_inclusion {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [PolynormableSpace ℂ E] {D : Set E} (hD : IsBanachDisc D) :
    Continuous (fun z : WithLocalSeminorm (gaugeSeminorm hD.balanced hD.convex hD.absorbent) ↦
      (show Submodule.span ℂ D from z).val) := by
  let G := WithLocalSeminorm (gaugeSeminorm hD.balanced hD.convex hD.absorbent)
  let i : G →ₗ[ℂ] E := (Submodule.span ℂ D).subtype
  let hE := PolynormableSpace.withSeminorms ℂ E
  refine hE.continuous_of_continuous_comp i fun j ↦ ?_
  obtain ⟨R, _, hR⟩ := hE.isVonNBounded_iff_seminorm_bounded.mp hD.bounded j
  refine Seminorm.continuous' (r := R) (mem_of_superset (Metric.ball_mem_nhds (0 : G) one_pos) ?_)
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hzD : (show Submodule.span ℂ D from z) ∈ ((↑) ⁻¹' D : Set (Submodule.span ℂ D)) :=
    setOfPred_gauge_lt_one_subset_self hD.convex hD.absorbent.zero_mem hD.absorbent hz
  rw [Seminorm.mem_closedBall_zero]
  exact (hR (i z) hzD).le

/-- Synthesis of an absolutely summable, uniformly seminorm-bounded series into a Banach space. -/
private theorem spectralTrace_boundedSeries_toBanach {E Y : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [SeminormedAddCommGroup Y] [NormedSpace ℂ Y] [T2Space Y] [CompleteSpace Y]
    (L : ℕ → StrongDual ℂ E) (b : ℕ → Y) (a : ℕ → ℂ) (ha : Summable (fun n ↦ ‖a n‖))
    (q : Seminorm ℂ E) (hq : Continuous q) (hL : ∀ n x, ‖L n x‖ ≤ q x) (hb : ∀ n, ‖b n‖ ≤ 1) :
    ∃ analysisMap : E →L[ℂ] Y, ∀ x, HasSum (fun n ↦ (a n * L n x) • b n) (analysisMap x) := by
  let term (x : E) (n : ℕ) := (a n * L n x) • b n
  have bound (x : E) (n : ℕ) : ‖term x n‖ ≤ ‖a n‖*q x := by
    calc
      _ = ‖a n‖*‖L n x‖*‖b n‖ := by simp only [term,norm_smul,norm_mul]
      _ ≤ ‖a n‖*q x*1 := by gcongr <;> first | exact hL _ _ | exact hb _
      _ = _ := mul_one _
  have hs (x : E) : Summable (term x) := (ha.mul_right (q x)).of_norm_bounded (bound x)
  let analysisMap : E →ₗ[ℂ] Y := {
    toFun x := ∑' n, term x n
    map_add' x y := ((hs (x+y)).hasSum.unique <| ((hs x).hasSum.add (hs y).hasSum).congr_fun (fun n ↦
      by simp only [term,map_add,mul_add,add_smul]))
    map_smul' c x := ((hs (c • x)).hasSum.unique <| ((hs x).hasSum.const_smul c).congr_fun (fun n ↦
      by simp only [term,map_smul,smul_eq_mul,smul_smul]; ring_nf)) }
  let M := ∑' n, ‖a n‖
  have hM : 0 ≤ M := tsum_nonneg (fun _ ↦ norm_nonneg _)
  have dominated (x : E) : ‖analysisMap x‖ ≤ M * q x := by
    calc
      _ ≤ ∑' n, ‖a n‖*q x := by
        have hnorm := Summable.of_nonneg_of_le (fun n ↦ norm_nonneg (term x n)) (bound x) (ha.mul_right (q x))
        exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum (bound x) (ha.mul_right (q x)))
      _ = M*q x := tsum_mul_right
  let p := M.toNNReal • q
  have hp (x : E) : p x = M*q x := by simp [p,NNReal.smul_def,hM,Real.toNNReal_of_nonneg]
  have hpcont : Continuous p := by simpa only [show (⇑p) = (fun x ↦ M*q x) from funext hp] using hq.const_mul M
  have hU : Continuous analysisMap := (PolynormableSpace.withSeminorms ℂ E).continuous_normedSpace_rng Y analysisMap
    ⟨{⟨p,hpcont⟩},1,by simpa using (show (normSeminorm ℂ Y).comp analysisMap ≤ p from fun x ↦ (dominated x).trans_eq (hp x).symm)⟩
  exact ⟨⟨analysisMap,hU⟩,fun x ↦ (hs x).hasSum⟩

/-- Factor a rapid presentation through ℓ² by giving the synthesis vectors the weights `(n + 1)⁻²`.
Project away the kernel of synthesis to obtain an injective Hilbert-to-quotient map. -/
private theorem spectralTrace_rapidPresentation_hilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
    (T : E →L[ℂ] E) (r : NuclearPresentation T)
    (hr : ∀ k : ℕ, ∃ C : ℝ, ∀ n, ‖r.coeff n‖*((n:ℝ)+1)^k ≤ C) :
    ∃ W : Submodule ℂ (lp (fun _ : ℕ ↦ ℂ) 2), IsClosed (W : Set (lp (fun _ : ℕ ↦ ℂ) 2)) ∧
      ∃ (analysisMap : E →L[ℂ] W) (synthesisMap : W →L[ℂ] E) (a : ℕ → ℂ) (b : ℕ → W), Injective synthesisMap ∧
        (∀ x, synthesisMap (analysisMap x) = T x) ∧ Summable (fun n ↦ ‖a n‖) ∧ (∀ n, ‖b n‖ ≤ 1) ∧
        (∀ x, HasSum (fun n ↦ (a n*r.functional n x) • b n) (analysisMap x)) ∧
        ∀ n, a n • synthesisMap (b n) = r.coeff n • (r.vector n).val := by
  let H := (lp (fun _ : ℕ ↦ ℂ) 2)
  let β (n : ℕ) := (((n:ℝ)+1)^2)⁻¹
  let α (n : ℕ) : ℂ := r.coeff n * (((n:ℂ)+1)^2)
  have hβ : Summable β := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
    simpa only [β,one_div,Nat.cast_add,Nat.cast_one] using h
  have hβn (n : ℕ) : ‖(β n:ℂ)‖ = β n := by rw [Complex.norm_real,Real.norm_of_nonneg (by dsimp [β]; positivity)]
  have ha : Summable (fun n ↦ ‖α n‖) := by
    obtain ⟨C,hC⟩ := hr 4
    apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ (hβ.mul_left C)
    intro n
    have hnc : ‖(n:ℂ)+1‖ = (n:ℝ)+1 := by
      rw [←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_add,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    change ‖r.coeff n * (((n:ℂ)+1)^2)‖ ≤ C / _
    rw [norm_mul,norm_pow,hnc,le_div_iff₀ (by positivity)]
    simpa only [mul_assoc,←pow_add] using hC n
  have hαβ (n : ℕ) : α n*(β n:ℂ) = r.coeff n := by
    dsimp only [α,β]; push_cast; field_simp
  let e (n : ℕ) : H := lp.single 2 n (1:ℂ)
  have he (n : ℕ) : ‖e n‖ ≤ 1 := by simp only [e,lp.norm_single (by norm_num : (0:ENNReal)<2),norm_one,le_refl]
  have hqfa := ((norm_withSeminorms ℂ ℂ).equicontinuous_tfae (fun n ↦ (r.functional n).toLinearMap)).out 1 4
  obtain ⟨q,hq,hqL⟩ := (hqfa.mp r.equicontinuous) ()
  obtain ⟨analysisMap,hU⟩ := spectralTrace_boundedSeries_toBanach r.functional e α ha q hq hqL he
  let G := WithLocalSeminorm (gaugeSeminorm r.isBanachDisc.balanced r.isBanachDisc.convex r.isBanachDisc.absorbent)
  let : CompleteSpace G := r.isBanachDisc.complete
  let : T2Space G := r.isBanachDisc.separated
  let j : G →L[ℂ] E := ⟨(Submodule.span ℂ r.disc).subtype,spectralTrace_banachDisc_inclusion r.isBanachDisc⟩
  let y (n : ℕ) : G := r.vector n
  have hy (n : ℕ) : ‖y n‖ ≤ 1 := gauge_le_one_of_mem (show r.vector n ∈ ((↑) ⁻¹' r.disc : Set (Submodule.span ℂ r.disc)) from r.vector_mem n)
  let eval (n : ℕ) : H →L[ℂ] ℂ := lp.evalCLM ℂ _ 2 n
  obtain ⟨Vg,hVg⟩ := spectralTrace_boundedSeries_toBanach eval y (fun n ↦ (β n:ℂ)) (by simpa only [hβn] using hβ)
    (normSeminorm ℂ H) continuous_norm (fun n x ↦ lp.norm_apply_le_norm (by norm_num) x n) hy
  let synthesisMap := j.comp Vg
  have hVe (n : ℕ) : synthesisMap (e n) = (β n:ℂ) • (r.vector n).val := by
    have hg : Vg (e n) = (β n:ℂ) • y n := by
      apply (hVg (e n)).unique
      have heval (k : ℕ) : eval k (e n) = if k=n then 1 else 0 := by
        change (lp.single (E := fun _ : ℕ ↦ ℂ) 2 n (1:ℂ)) k = _
        simp [lp.single_apply,Pi.single_apply,eq_comm]
      have hs := hasSum_single n (f := fun k ↦ ((β k:ℂ)*eval k (e n)) • y k) (fun k hkn ↦ by simp [heval,hkn])
      exact (show (β n:ℂ) • y n = ((β n:ℂ)*eval n (e n)) • y n by rw [heval]; simp) ▸ hs
    change j (Vg (e n)) = _
    rw [hg,map_smul]; rfl
  have hVU (x : E) : synthesisMap (analysisMap x) = T x := by
    refine ((hU x).mapL synthesisMap).unique ((r.hasSum x).congr_fun (fun n ↦ ?_))
    rw [map_smul,hVe,smul_smul,mul_right_comm,hαβ]
  let K := synthesisMap.toLinearMap.ker
  let : CompleteSpace K := synthesisMap.isClosed_ker.completeSpace_coe
  let W := Kᗮ
  let : CompleteSpace W := K.isClosed_orthogonal.completeSpace_coe
  let π := W.orthogonalProjectionOnto
  have hπ (x : H) : synthesisMap (π x).val = synthesisMap x := by
    have hx : x-(π x).val ∈ K := by
      simpa only [W,K.orthogonal_orthogonal,Submodule.starProjection_apply] using Submodule.sub_starProjection_mem_orthogonal (K := W) x
    change synthesisMap (x-(π x).val) = 0 at hx
    exact ((sub_eq_zero.mp <| (map_sub synthesisMap _ _) ▸ hx)).symm
  refine ⟨W,K.isClosed_orthogonal,π.comp analysisMap,synthesisMap.comp W.subtypeL,α,fun n ↦ π (e n),?_,
    fun x ↦ (hπ (analysisMap x)).trans (hVU x),ha,fun n ↦ (W.norm_orthogonalProjectionOnto_apply_le _).trans (he n),?_,?_⟩
  · change Injective (synthesisMap.comp W.subtypeL).toLinearMap
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    exact Subtype.ext ((Submodule.disjoint_def.mp K.isCompl_orthogonal.disjoint) _ hx x.property)
  · intro x
    simpa only [map_smul,ContinuousLinearMap.comp_apply] using (hU x).mapL π
  · intro n
    change α n • synthesisMap (π (e n)).val = _
    rw [hπ,hVe,smul_smul,hαβ]

/-- The Hilbert representation of a finite spectral mask computes its algebraic trace
without any estimate on the original (possibly very oblique) mask. -/
private theorem spectralTrace_rectangular {E H : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (u : E →L[ℂ] H) (v : H →L[ℂ] E)
    (p : E →L[ℂ] E) (hid : ∀ x, p (p x) = p x) (hc : ∀ x, v (u (p x)) = p (v (u x)))
    (hfin : FiniteDimensional ℂ p.toLinearMap.range)
    (R : p.toLinearMap.range →ₗ[ℂ] p.toLinearMap.range) (hR : ∀ x, (R x).val = v (u x.val)) :
    let K := (p.comp v).toLinearMap.ker
    let W := Kᗮ
    FiniteDimensional ℂ W ∧
      LinearMap.trace ℂ W ((W.orthogonalProjectionOnto.comp ((u.comp v).comp W.subtypeL)).toLinearMap) =
        LinearMap.trace ℂ _ R := by
  classical
  intro K W
  let : CompleteSpace W := K.isClosed_orthogonal.completeSpace_coe
  let : CompleteSpace K := (p.comp v).isClosed_ker.completeSpace_coe
  let A : W →ₗ[ℂ] p.toLinearMap.range := (p.toLinearMap.rangeRestrict.comp v.toLinearMap).comp W.subtype
  have hA (x : W) : (A x).val = p (v x.val) := rfl
  have hinj : Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have he : x.val ∈ K := congrArg Subtype.val hx
    exact Subtype.ext ((Submodule.disjoint_def.mp K.isCompl_orthogonal.disjoint) _ he x.property)
  let : FiniteDimensional ℂ W := FiniteDimensional.of_injective A hinj
  refine ⟨inferInstance,?_⟩
  let backward := (W.orthogonalProjectionOnto.toLinearMap.comp u.toLinearMap).comp p.toLinearMap.range.subtype
  have hpk (y : H) : p (v (W.orthogonalProjectionOnto y).val) = p (v y) := by
    have he := Submodule.sub_starProjection_mem_orthogonal (K := W) y
    have hk : y - (W.orthogonalProjectionOnto y).val ∈ K := by simpa only [W,K.orthogonal_orthogonal,Submodule.starProjection_apply] using he
    change p (v (y - (W.orthogonalProjectionOnto y).val)) = 0 at hk
    rw [map_sub,map_sub,sub_eq_zero] at hk
    exact hk.symm
  have hpu (x : E) : W.orthogonalProjectionOnto (u (p x)) = W.orthogonalProjectionOnto (u x) := by
    apply sub_eq_zero.mp
    rw [←map_sub]
    change u (p x) - u x ∈ W.orthogonalProjectionOnto.ker
    rw [Submodule.ker_orthogonalProjectionOnto]
    change u (p x)-u x ∈ Kᗮᗮ
    rw [K.orthogonal_orthogonal]
    change p (v (u (p x)-u x)) = 0
    rw [map_sub,map_sub,hc,hid,sub_self]
  have compW : backward.comp A = (W.orthogonalProjectionOnto.comp ((u.comp v).comp W.subtypeL)).toLinearMap := by
    apply LinearMap.ext
    intro x
    change W.orthogonalProjectionOnto (u (p (v x.val))) = _
    exact hpu _
  have compE : A.comp backward = R := by
    ext x
    change p (v (W.orthogonalProjectionOnto (u x.val)).val) = (R x).val
    rw [hpk,hR,←hc]
    obtain ⟨z,hz⟩ := x.property
    change p z = x.val at hz
    rw [←hz,hid]
  rw [←compW,←compE]
  exact LinearMap.trace_comp_comm' _ _

/-- Any pointwise absolutely converging rank-one expansion on a finite-dimensional Hilbert
space gives its algebraic trace by contraction. -/
private theorem spectralTrace_finiteDimensional_series {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (T : H →ₗ[ℂ] H) (a : ℕ → ℂ) (L : ℕ → StrongDual ℂ H) (b : ℕ → H)
    (hT : ∀ x, HasSum (fun n ↦ (a n * L n x) • b n) (T x)) :
    HasSum (fun n ↦ a n * L n (b n)) (LinearMap.trace ℂ H T) := by
  classical
  let e := stdOrthonormalBasis ℂ H
  let D := Fin (Module.finrank ℂ H)
  let c (i : D) := innerSL ℂ (e i)
  have hs (i : D) (_ : i ∈ (Finset.univ : Finset D)) :
      HasSum (fun n ↦ (a n * L n (e i)) * c i (b n)) (c i (T (e i))) := by
    simpa only [map_smul,smul_eq_mul] using (hT (e i)).mapL (c i)
  have hsum := hasSum_sum hs
  have he (n : ℕ) : ∑ i : D, (a n*L n (e i))*c i (b n) = a n*L n (b n) := by
    calc
      _ = a n * L n (∑ i, c i (b n) • e i) := by
        simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
      _ = _ := congrArg (fun y ↦ a n * L n y) (e.sum_repr' (b n))
  have ht : LinearMap.trace ℂ H T = ∑ i : D, c i (T (e i)) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ e.toBasis,Matrix.trace]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.diag_apply,LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.repr_apply_apply,c,innerSL_apply_apply]
  simpa only [ht,he] using hsum

/-- Finite supported trace approximations identify the numerical trace of an already rapid
presentation, irrespective of whether the cutoff operators are equicontinuous. -/
private theorem spectralTrace_of_finiteProjections {E Z : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
    (T : E →L[ℂ] E) (r : NuclearPresentation T)
    (hr : ∀ k : ℕ, ∃ C : ℝ, ∀ n, ‖r.coeff n‖*((n:ℝ)+1)^k ≤ C)
    (p : Finset Z → E →L[ℂ] E) (R : (C : Finset Z) → (p C).toLinearMap.range →ₗ[ℂ] (p C).toLinearMap.range)
    (hid : ∀ C x, p C (p C x) = p C x) (hc : ∀ C x, T (p C x) = p C (T x))
    (hfin : ∀ C, FiniteDimensional ℂ (p C).toLinearMap.range) (hR : ∀ C x, (R C x).val = T x.val)
    (hanti : ∀ C D, C ⊆ D → (p D).toLinearMap.ker ≤ (p C).toLinearMap.ker)
    (hsep : ∀ x, (∀ C, p C x = 0) → x=0) (t : ℂ)
    (hlen : Tendsto (fun C ↦ LinearMap.trace ℂ _ (R C)) atTop (𝓝 t)) :
    HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) t := by
  classical
  obtain ⟨H,hclosed,analysisMap,synthesisMap,a,b,hV,hvu,ha,hb,hU,hvec⟩ := spectralTrace_rapidPresentation_hilbert T r hr
  let : CompleteSpace H := hclosed.completeSpace_coe
  let K (C : Finset Z) := ((p C).comp synthesisMap).toLinearMap.ker
  let W (C : Finset Z) := (K C)ᗮ
  let (C : Finset Z) : CompleteSpace (K C) := ((p C).comp synthesisMap).isClosed_ker.completeSpace_coe
  let (C : Finset Z) : CompleteSpace (W C) := (K C).isClosed_orthogonal.completeSpace_coe
  have mono : Monotone W := by
    intro c d hcd
    apply Submodule.orthogonal_le
    exact fun x hx ↦ hanti c d hcd hx
  have dense : ⊤ ≤ (⨆ C, W C).topologicalClosure := by
    apply (Submodule.topologicalClosure_eq_top_iff.mpr ?_).ge
    rw [Submodule.eq_bot_iff]
    intro x hx
    apply hV
    rw [map_zero]
    apply hsep
    intro C
    have hm : x ∈ (W C)ᗮ := Submodule.orthogonal_le (le_iSup W C) hx
    change x ∈ K C
    simpa only [W,(K C).orthogonal_orthogonal] using hm
  have limit (y : H) := Submodule.starProjection_tendsto_self W mono y dense
  -- Contract in the orthogonal Hilbert cutoffs, whose operator norms are at most one.
  have hrect (C : Finset Z) := spectralTrace_rectangular analysisMap synthesisMap (p C) (hid C)
    (fun x ↦ by rw [hvu,hvu,hc]) (hfin C) (R C) (fun x ↦ (hR C x).trans (hvu x.val).symm)
  let d (C : Finset Z) (n : ℕ) := a n * r.functional n (synthesisMap ((W C).starProjection (b n)))
  have loc (C : Finset Z) : HasSum (d C) (LinearMap.trace ℂ _ (R C)) := by
    let : FiniteDimensional ℂ (W C) := (hrect C).1
    let π := (W C).orthogonalProjectionOnto
    let S := (π.comp ((analysisMap.comp synthesisMap).comp (W C).subtypeL)).toLinearMap
    let L (n : ℕ) := (r.functional n).comp (synthesisMap.comp (W C).subtypeL)
    have row (x : W C) : HasSum (fun n ↦ (a n * L n x) • π (b n)) (S x) := by
      simpa only [L,S,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,ContinuousLinearMap.coe_coe,map_smul] using
        (hU (synthesisMap x.val)).mapL π
    have hl := spectralTrace_finiteDimensional_series S a L (fun n ↦ π (b n)) row
    have he : LinearMap.trace ℂ _ S = LinearMap.trace ℂ _ (R C) := (hrect C).2
    rw [←he]
    exact hl
  have hqfa := ((norm_withSeminorms ℂ ℂ).equicontinuous_tfae (fun n ↦ (r.functional n).toLinearMap)).out 1 4
  obtain ⟨q,hq,hqL⟩ := (hqfa.mp r.equicontinuous) ()
  obtain ⟨M,hM,hbound⟩ := (q.comp synthesisMap.toLinearMap).bound_of_continuous_normedSpace (hq.comp synthesisMap.continuous)
  have unif (n : ℕ) (y : H) (hy : ‖y‖ ≤ 1) : ‖r.functional n (synthesisMap y)‖ ≤ M :=
    (hqL n (synthesisMap y)).trans ((hbound y).trans (mul_le_of_le_one_right hM.le hy))
  let scalar (n : ℕ) := a n * r.functional n (synthesisMap (b n))
  have normD (C : Finset Z) (n : ℕ) : ‖d C n‖ ≤ ‖a n‖*M := by
    change ‖a n * _‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (unif n _ (((W C).norm_starProjection_apply_le _).trans (hb _))) (norm_nonneg _)
  have hscalar (n : ℕ) : scalar n = r.coeff n * r.functional n (r.vector n).val := by
    simpa only [scalar,map_smul,smul_eq_mul] using congrArg (r.functional n) (hvec n)
  have limD (n : ℕ) : Tendsto (fun C ↦ d C n) atTop (𝓝 (scalar n)) :=
    (((r.functional n).continuous.comp synthesisMap.continuous).continuousAt.tendsto.comp (limit (b n))).const_mul _
  -- Tannery’s theorem exchanges the finite-cluster limit with the presentation series.
  have limTotal := tendsto_tsum_of_dominated_convergence (ha.mul_right M) limD
    (Eventually.of_forall normD)
  have hsum : Summable scalar := (ha.mul_right M).of_norm_bounded fun n ↦
    (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_left (unif n _ (hb n)) (norm_nonneg _))
  have val : (∑' n,scalar n) = t := tendsto_nhds_unique limTotal (hlen.congr fun C ↦ (loc C).tsum_eq.symm)
  exact val ▸ hsum.hasSum.congr_fun (fun n ↦ (hscalar n).symm)

open Classical in
/-- Every rapid presentation of the retained jet-endomorphism has the predicted divisor trace. -/
private theorem spectralNuclearity_trace_of_rapid_presentation (a : ℝ) (N : ℕ) (φ : 𝒟)
    (d : jets(χ,τ,hτ) → StrongDual ℂ (Q(a)))
    (hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val-(a:ℂ))) :
    let I := {i : jets(χ,τ,hτ) // i.2.val < N}
    let K := ⨅ i : I, (d i.val).toLinearMap.ker
    let E := Q(a) ⧸ K
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    let Z := zeros(χ,τ,hτ)
    let term (z : Z) := ((min N (multiplicity(χ,τ,hτ,z)) : ℕ):ℂ) * nuclearityTestMellin χ φ (z.val-(a:ℂ))
    ∀ (A : B →L[ℂ] B) (Aq : Q(a) →L[ℂ] Q(a)) (T : E →L[ℂ] E),
      (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) →
      (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) → (∀ x, T (K.mkQ x) = K.mkQ (Aq x)) →
      ∀ r : NuclearPresentation T, (∀ k : ℕ, ∃ C : ℝ, ∀ n, ‖r.coeff n‖*((n:ℝ)+1)^k ≤ C) →
        HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) (∑' z,term z) := by
  classical
  intro I K E Z term A Aq T hA hAq hT r hr
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let D := D(a)
  let : IsClosed (D : Set B) := schwartzBergmanDivisible_isClosed _
  have hB : IsNuclearTVS.{0} B := spectralJet_sb_nuclear
  let : T2Space B := hB.1
  let : PolynormableSpace ℂ B := hB.2.1
  let : T2Space (Q(a)) := inferInstanceAs (T2Space (B ⧸ D))
  have hQ : IsNuclearTVS.{0} (Q(a)) := isNuclearTVS_quotient hB D
  let : PolynormableSpace ℂ (Q(a)) := hQ.2.1
  let : IsClosed (K : Set (Q(a))) := by
    change IsClosed (↑(⨅ i : I, (d i.val).toLinearMap.ker) : Set (Q(a)))
    rw [Submodule.coe_iInf]
    exact isClosed_iInter (fun i ↦ (d i.val).isClosed_ker)
  let : T2Space E := inferInstanceAs (T2Space (Q(a) ⧸ K))
  let : PolynormableSpace ℂ E := (isNuclearTVS_quotient hQ K).2.1
  let L (i : I) : StrongDual ℂ E := ⟨K.liftQ (d i.val).toLinearMap (iInf_le _ i),
    (Submodule.isQuotientMap_mkQ K).continuous_iff.mpr (d i.val).continuous⟩
  have hL (i : I) (x : Q(a)) : L i (K.mkQ x) = d i.val x := rfl
  have separates (x : E) (hx : ∀ i, L i x=0) : x=0 := by
    obtain ⟨y,rfl⟩ := K.mkQ_surjective x
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,Submodule.mem_iInf]
    exact fun i ↦ hx i
  choose proj hmask hid hcomm hfin Rq _ using
    spectralNuclearity_trace_finite_cluster χ τ hτ a N φ d hd A Aq T hA hAq hT L hL
  choose R hR htrace using Rq
  refine spectralTrace_of_finiteProjections T r hr proj R hid hcomm hfin hR ?_ ?_ _ ?_
  · intro c e hce x hx
    change proj c x = 0
    apply separates
    intro i
    rw [hmask]
    by_cases hi : i.val.1 ∈ c
    · rw [ite_eq_left hi]
      have hm := hmask e i x
      change proj e x = 0 at hx
      simpa only [hx,map_zero,ite_eq_left (hce hi)] using hm.symm
    · rw [ite_eq_right hi]
  · intro x hx
    apply separates
    intro i
    have hm := hmask {i.val.1} i x
    simpa only [hx,map_zero,Finset.mem_singleton_self,ite_true] using hm.symm
  · have hs : Summable term := Summable.of_norm (spectralNuclearity_trace_term_summable χ τ hτ a N φ)
    have e : (fun C : Finset Z ↦ LinearMap.trace ℂ _ (R C)) = (fun C ↦ ∑ z ∈ C,term z) := funext htrace
    rw [e]
    exact hs.hasSum

end SpectralTraceHilbert

section SpectralBoundarySynthesis

open Filter Function Set Topology Bornology MeasureTheory Asymptotics Metric
open scoped NNReal ENNReal

/-- A separating family of observations has strongly dense span in the dual of
a space on which every continuous strong-bidual element is evaluation. -/
private theorem spectralBoundary_dense_observations {S I : Type*}
    [AddCommGroup S] [Module ℂ S] [TopologicalSpace S] [IsTopologicalAddGroup S]
    [ContinuousSMul ℂ S] [PolynormableSpace ℂ S] [T2Space S]
    (obs : I → StrongDual ℂ S) (separate : ∀ x : S, (∀ i, obs i x=0) → x=0)
    (bidual : ∀ φ : StrongDual ℂ (StrongDual ℂ S), ∃ x : S, ∀ L, φ L = L x) :
    Dense ((Submodule.span ℂ (range obs)) : Set (StrongDual ℂ S)) := by
  let : UniformSpace S := IsTopologicalAddGroup.rightUniformSpace S
  let : IsUniformAddGroup S := isUniformAddGroup_of_addCommGroup
  let X := StrongDual ℂ S
  let D := Submodule.span ℂ (range obs)
  let : PolynormableSpace ℂ X :=
    uniformConvergenceCLM_polynormable (F := ℂ)
      {T : Set S | IsVonNBounded ℂ T} (fun _ h ↦ h)
      (by rw [Bornology.sUnion_isVonNBounded_eq_univ,Submodule.span_univ];simp)
  let : Module ℝ X := Module.restrictScalars ℝ ℂ X
  let : IsScalarTower ℝ ℂ X := IsScalarTower.restrictScalars ℝ ℂ X
  let : LocallyConvexSpace ℝ X :=
    (PolynormableSpace.withSeminorms ℂ X).toLocallyConvexSpace
  intro L
  change L ∈ D.topologicalClosure
  by_contra hn
  obtain ⟨φ,hφ,hzero⟩ := exists_dual_eq_zero_on_submodule_of_notMem
    D.topologicalClosure D.isClosed_topologicalClosure hn
  obtain ⟨x,hx⟩ := bidual φ
  have h0 : x=0 := separate x fun i ↦ (hx _).symm.trans
    (hzero _ (D.le_topologicalClosure (Submodule.subset_span (mem_range_self i))))
  exact hφ (by rw [hx,h0,map_zero])

/-- Locally bounded Schwartz-valued kernels can be tested for weak holomorphy on a
separating family. Strong-dual approximation is uniform on the bounded family. -/
private theorem spectralBoundary_weak_holomorphic {S I : Type*}
    [AddCommGroup S] [Module ℂ S] [TopologicalSpace S] [IsTopologicalAddGroup S]
    [ContinuousSMul ℂ S] [PolynormableSpace ℂ S] [T2Space S]
    (obs : I → StrongDual ℂ S) (hd : Dense ((Submodule.span ℂ (range obs)) : Set (StrongDual ℂ S)))
    (region : Set ℂ) (hU : IsOpen region) (f : ℂ → S) (hb : IsVonNBounded ℂ (f '' region))
    (ho : ∀ i, DifferentiableOn ℂ (fun z ↦ obs i (f z)) region) (L : StrongDual ℂ S) :
    DifferentiableOn ℂ (fun z ↦ L (f z)) region := by
  let D := Submodule.span ℂ (range obs)
  let pairing : Submodule ℂ (StrongDual ℂ S) :=
    { carrier := {l | DifferentiableOn ℂ (fun z ↦ l (f z)) region}
      zero_mem' := differentiableOn_const (0:ℂ)
      add_mem' := fun {x y} hx hy ↦ hx.add hy
      smul_mem' := fun c x hx ↦ hx.const_mul c }
  have hs : D ≤ pairing := Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩;exact ho i)
  let F := 𝓝[(D : Set (StrongDual ℂ S))] L
  let : F.NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hd L)
  have hlim : Tendsto (id : StrongDual ℂ S → StrongDual ℂ S) F (𝓝 L) := nhdsWithin_le_nhds
  have hv := (UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn (RingHom.id ℂ) ℂ
    {s : Set S | IsVonNBounded ℂ s}).mp hlim (f '' region) hb
  have hv' : TendstoUniformlyOn (fun l z ↦ l (f z)) (fun z ↦ L (f z)) F region :=
    (hv.comp f).mono (fun x hx ↦ mem_image_of_mem _ hx)
  have hm : ∀ᶠ l in F, l ∈ D := self_mem_nhdsWithin
  have hP : ∀ᶠ l in F, DifferentiableOn ℂ (fun z ↦ l (f z)) region :=
    hm.mono fun l hl ↦ hs hl
  exact hv'.tendstoLocallyUniformlyOn.differentiableOn hP hU

/-- The evaluation functionals at individual real points are dense in the strong dual
of the complex real-line Schwartz space. -/
private theorem spectralBoundary_schwartz_eval_dense :
    let eval (t : ℝ) := (BoundedContinuousFunction.evalCLM ℂ t).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)
    Dense ((Submodule.span ℂ (range eval)) : Set (StrongDual ℂ (SchwartzMap ℝ ℂ))) := by
  intro eval
  let S := SchwartzMap ℝ ℂ
  let : PolynormableSpace ℂ S := (schwartz_withSeminorms ℂ ℝ ℂ).toPolynormableSpace
  apply spectralBoundary_dense_observations eval (fun x h ↦ SchwartzMap.ext h)
  let D := EuclideanSpace ℝ (Fin 1)
  let E := SchwartzMap D ℂ
  let e : S ≃L[ℂ] E := schwartzChangeVariable ℂ (PiLp.equivOfUnique 2 ℝ _ : D ≃L[ℝ] ℝ)
  let lift : StrongDual ℂ E →L[ℂ] StrongDual ℂ S :=
    ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ e.toContinuousLinearMap
  obtain ⟨j,hj⟩ := euclideanSchwartz_reflexive 1
  intro Φ
  obtain ⟨u,hu⟩ := j.surjective (Φ.comp lift)
  refine ⟨e.symm u,fun L ↦ ?_⟩
  let l := L.comp e.symm.toContinuousLinearMap
  have eqL : lift l = L := by ext x; change L (e.symm (e x)) = L x; rw [e.symm_apply_apply]
  calc
    Φ L = (Φ.comp lift) l := by change Φ L = Φ (lift l); rw [eqL]
    _ = j u l := by rw [hu]
    _ = l u := hj u l
    _ = _ := rfl

/-- In a locally bounded family of real-line Schwartz functions, holomorphy of
every point value implies holomorphy after application of any tempered functional. -/
private theorem spectralBoundary_schwartz_dual_holomorphic (region : Set ℂ) (hU : IsOpen region)
    (f : ℂ → SchwartzMap ℝ ℂ) (hb : IsVonNBounded ℂ (f '' region))
    (hf : ∀ t : ℝ, DifferentiableOn ℂ (fun z ↦ f z t) region) (L : StrongDual ℂ (SchwartzMap ℝ ℂ)) :
    DifferentiableOn ℂ (fun z ↦ L (f z)) region := by
  let : PolynormableSpace ℂ (SchwartzMap ℝ ℂ) := (schwartz_withSeminorms ℂ ℝ ℂ).toPolynormableSpace
  exact spectralBoundary_weak_holomorphic _ spectralBoundary_schwartz_eval_dense region hU f hb hf L

/-- Every tempered functional applied to a pointwise holomorphic Schwartz-valued
kernel with bounded weighted strip families gives an entire Schwartz–Bergman function. -/
private theorem spectralBoundary_synthesis_schwartzBergman (K : ℂ → SchwartzMap ℝ ℂ)
    (hk : ∀ t : ℝ, Differentiable ℂ (fun z ↦ K z t))
    (hb : ∀ (A : ℝ) (p : ℕ), IsVonNBounded ℂ
      (range (fun z : {z : ℂ // |z.re| ≤ A} ↦ (((1+|z.val.im|)^p:ℝ):ℂ) • K z.val))) :
    ∃ R : StrongDual ℂ (SchwartzMap ℝ ℂ) →ₗ[ℂ] SchwartzBergman (univ : Set ℝ),
      ∀ L z, (R L).val z = L (K z) := by
  let S := SchwartzMap ℝ ℂ
  let sourceSpace := SchwartzBergman (univ : Set ℝ)
  have mem (L : StrongDual ℂ S) : (fun z ↦ L (K z)) ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
    have hdiff : Differentiable ℂ (fun z ↦ L (K z)) := by
      intro z
      let A := |z.re|+1
      let region := {v : ℂ | |v.re| < A}
      have Uop : IsOpen region := isOpen_lt Complex.continuous_re.abs continuous_const
      have hz : z ∈ region := by dsimp [region,A]; linarith
      have b0 : IsVonNBounded ℂ (K '' region) := (hb A 0).subset (by
        rintro _ ⟨w,hw,rfl⟩
        exact ⟨⟨w,le_of_lt hw⟩,by simp⟩)
      exact (spectralBoundary_schwartz_dual_holomorphic region Uop K b0
        (fun t ↦ (hk t).differentiableOn) L z hz).differentiableAt (Uop.mem_nhds hz)
    refine ⟨fun z h ↦ (h (mem_univ _)).elim,hdiff.differentiableOn,?_⟩
    intro a b _ _ n
    let A := |a|+|b|
    have hA : 0 ≤ A := by dsimp [A]; positivity
    obtain ⟨C,hC⟩ := ((NormedSpace.isVonNBounded_iff ℂ).mp ((hb A n).image L)).exists_norm_le
    refine ⟨(1+A)^n*C,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    have hr : |z.re| ≤ A := abs_le.mpr ⟨by dsimp [A]; linarith [hz.1,neg_abs_le a,abs_nonneg b],
      by dsimp [A]; linarith [hz.2,le_abs_self b,abs_nonneg a]⟩
    have hzn := hC _ (mem_image_of_mem L (mem_range_self (⟨z,hr⟩ : {z : ℂ // |z.re| ≤ A})))
    change ‖L ((((1+|z.im|)^n:ℝ):ℂ) • K z)‖ ≤ C at hzn
    rw [map_smul, norm_smul, Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (1+|z.im|)^n by positivity)] at hzn
    have hn : ‖z‖ ≤ (1+A)*(1+|z.im|) := (Complex.norm_le_abs_re_add_abs_im z).trans (by nlinarith [mul_nonneg hA (abs_nonneg z.im)])
    change ‖z^n * L (K z)‖ ≤ _
    rw [norm_mul,norm_pow]
    calc
      _ ≤ ((1+A)*(1+|z.im|))^n * ‖L (K z)‖ := by gcongr
      _ = (1+A)^n * ((1+|z.im|)^n*‖L (K z)‖) := by rw [mul_pow,mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left hzn (by positivity)
  exact ⟨{toFun := fun L ↦ ⟨fun z ↦ L (K z),mem L⟩
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl},fun _ _ ↦ rfl⟩

open scoped NNReal ENNReal

private theorem spectralBoundary_rapidBound_eq (a : (Fin 1 → ℤ) → ℂ) (j : ℕ) :
    rapidDecaySequenceBound j a =
      ∑' n, ENNReal.ofReal (latticeWeight n ^ j * ‖a (latticeIndex n)‖) := by
  unfold rapidDecaySequenceBound
  rw [← latticeIndex.tsum_eq]
  apply tsum_congr
  intro n
  have hw : 0 ≤ latticeWeight n := zero_le_one.trans (latticeWeight_bounds n).1
  rw [ENNReal.ofReal_mul (pow_nonneg hw _), ENNReal.ofReal_pow hw, ofReal_norm]
  congr 2
  rw [latticeWeight, ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one]
  congr 1
  change ‖(WithLp.toLp 2 (fun i ↦ ((latticeIndex n i : ℤ) : ℝ)) : EuclideanSpace ℝ (Fin 1))‖ₑ = _
  rw [← ofReal_norm, EuclideanSpace.norm_eq]
  simp [latticeIndex, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

private theorem spectralBoundary_rapidSeminorm_eq (a : RapidDecaySequence 1) (j : ℕ) :
    rapidDecaySequenceSeminorm j a = ∑' n, latticeWeight n ^ j * ‖a (latticeIndex n)‖ := by
  change (rapidDecaySequenceBound j a.val).toReal = _
  rw [spectralBoundary_rapidBound_eq, ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro n
  exact ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg (zero_le_one.trans (latticeWeight_bounds n).1) _)
    (norm_nonneg _))
/-- Continuous weighted analysis on a closed Hilbert boundary. The family is linear both
in the rapid sequence and in its ℓ² argument, with a single seminorm bound in each weight. -/
private theorem spectralBoundary_weighted_pair (k : ℕ) :
    let H := lp (fun _ : ℕ ↦ ℂ) 2
    let S := RapidDecaySequence 1
    ∃ L : H →ₗ[ℂ] StrongDual ℂ S,
      (∀ s : S, Continuous (fun h : H ↦ L h s)) ∧
      (∀ h s, L h s = ∑' n : ℕ, h n * ((latticeWeight n ^ k:ℝ):ℂ) * s (latticeIndex n)) ∧
      (∀ (n : ℕ) (s : S), L (lp.single (E := fun _ : ℕ ↦ ℂ) 2 n (1:ℂ)) s =
        ((latticeWeight n ^ k:ℝ):ℂ) * s (latticeIndex n)) := by
  intro H S
  let W (n : ℕ) : ℝ := latticeWeight n ^ k
  have hW (n : ℕ) : 0 ≤ W n := pow_nonneg (zero_le_one.trans (latticeWeight_bounds n).1) _
  let t (x : H) (s : S) (n : ℕ) := x n * (W n:ℂ) * s (latticeIndex n)
  have major (x : H) (s : S) (n : ℕ) : ‖t x s n‖ ≤ ‖x‖ * (W n * ‖s (latticeIndex n)‖) := by
    simp only [t,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hW n),mul_assoc]
    exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm (by norm_num) x n)
      (mul_nonneg (hW n) (norm_nonneg _))
  have hsum (s : S) : HasSum (fun n ↦ W n * ‖s (latticeIndex n)‖) (rapidDecaySequenceSeminorm k s) := by
    rw [spectralBoundary_rapidSeminorm_eq]
    exact ((rapidSequence_mem_iff s.val).mp s.property k).hasSum
  have hs (x : H) (s : S) : Summable (t x s) := ((hsum s).summable.mul_left ‖x‖).of_norm_bounded (major x s)
  have bound (x : H) (s : S) : ‖∑' n, t x s n‖ ≤ ‖x‖ * rapidDecaySequenceSeminorm k s := by
    refine (norm_tsum_le_tsum_norm (hs x s).norm).trans ?_
    rw [← ((hsum s).mul_left ‖x‖).tsum_eq]
    exact (hs x s).norm.tsum_le_tsum (major x s) ((hsum s).summable.mul_left ‖x‖)
  let ls (x : H) : S →ₗ[ℂ] ℂ :=
    { toFun := fun s ↦ ∑' n, t x s n
      map_add' := fun a b ↦ by
        rw [← (hs x a).tsum_add (hs x b)]
        exact tsum_congr fun n ↦ mul_add _ _ _
      map_smul' := fun c a ↦ by
        change (∑' n, t x (c • a) n) = c • (∑' n, t x a n)
        rw [← (hs x a).tsum_const_smul c]
        apply tsum_congr; intro n
        change x n * (W n:ℂ) * (c*a (latticeIndex n)) = c * (x n * (W n:ℂ) * a (latticeIndex n))
        ring }
  let L (x : H) : StrongDual ℂ S := ⟨ls x,by
    apply WithSeminorms.continuous_normedSpace_rng _ rapidDecaySequence_withSeminorms
    refine ⟨{k}, ⟨‖x‖,norm_nonneg _⟩,fun s ↦ ?_⟩
    change ‖(ls x) s‖ ≤ _
    exact (bound x s).trans (mul_le_mul_of_nonneg_left ((Finset.le_sup (f := rapidDecaySequenceSeminorm (r := 1)) (Finset.mem_singleton_self k)) s) (norm_nonneg x))⟩
  let l : H →ₗ[ℂ] StrongDual ℂ S :=
    { toFun := L
      map_add' := fun a b ↦ by
        ext s; change (∑' n, t (a+b) s n) = (∑' n, t a s n) + ∑' n, t b s n
        rw [← (hs a s).tsum_add (hs b s)]
        apply tsum_congr; intro n
        change (a n+b n)*(W n:ℂ)*s (latticeIndex n) = _
        simp [t, add_mul]
      map_smul' := fun c a ↦ by
        ext s
        change (∑' n, t (c • a) s n) = c • (∑' n, t a s n)
        rw [← (hs a s).tsum_const_smul c]
        apply tsum_congr; intro n
        change c * a n * (W n:ℂ) * s (latticeIndex n) = c*(a n*(W n:ℂ)*s (latticeIndex n))
        ring }
  refine ⟨l,fun s ↦ ?_,fun _ _ ↦ rfl,fun n s ↦ ?_⟩
  · let q : H →ₗ[ℂ] ℂ := (ContinuousLinearMap.applyₗ (E := S) ℂ (RingHom.id ℂ) s).toLinearMap.comp l
    exact (q.mkContinuous (rapidDecaySequenceSeminorm k s) (fun x ↦ (bound x s).trans_eq (mul_comm _ _))).continuous
  · change (∑' j, t (lp.single 2 n 1) s j) = _
    rw [tsum_eq_single n]
    · simp [t,lp.single_apply,W]
    · intro m hm
      simp [t,lp.single_apply,hm]

private theorem spectralBoundary_continuous_of_closedGraph {E Y : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [ContinuousSMul ℂ Y]
    (hE : IsFrechetTVS E) (hY : IsFrechetTVS Y)
    (T : E →ₗ[ℂ] Y) (hT : IsClosed (T.graph : Set (E × Y))) : Continuous T := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace E := hE.2.2.2
  have : CompleteSpace Y := hY.2.2.2
  have : TopologicalSpace.MetrizableSpace E := hE.2.2.1
  have : TopologicalSpace.MetrizableSpace Y := hY.2.2.1
  let Γ := T.graph
  have : CompleteSpace Γ := completeSpace_coe_iff_isComplete.mpr hT.isComplete
  have : IsUniformAddGroup Γ := Γ.toAddSubgroup.isUniformAddGroup
  have : TopologicalSpace.MetrizableSpace (E × Y) := inferInstance
  have : TopologicalSpace.MetrizableSpace Γ :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (Γ : Set (E × Y)))
  have : FirstCountableTopology Γ := inferInstance
  have : FirstCountableTopology E := inferInstance
  have : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace E := BaireSpace.of_completelyPseudoMetrizable
  let Pr : Γ →L[ℂ] E := (ContinuousLinearMap.fst ℂ E Y).comp Γ.subtypeL
  have hmem (x : E) : (x, T x) ∈ Γ := (LinearMap.mem_graph_iff _ _).mpr rfl
  have hval (p : Γ) : p.val.2 = T p.val.1 := (LinearMap.mem_graph_iff _ _).mp p.property
  have hinj : Injective Pr := fun p q h ↦ by
    have h1 : p.val.1 = q.val.1 := h
    exact Subtype.ext (Prod.ext h1 (by rw [hval, hval, h1]))
  have hsurj : Surjective Pr := fun x ↦ ⟨⟨(x, T x), hmem x⟩, rfl⟩
  have ho : IsOpenMap Pr := by
    apply isOpenMap_of_not_isMeagre_range Pr
    rw [hsurj.range_eq]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  let h : Γ ≃ₜ E :=
    (Equiv.ofBijective Pr ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen Pr.continuous ho
  refine (continuous_snd.comp (continuous_subtype_val.comp h.symm.continuous)).congr fun x ↦ ?_
  have h1 : (h.symm x).val.1 = x := h.apply_symm_apply x
  change (h.symm x).val.2 = T x
  rw [hval, h1]

/-- Applying the weighted rapid coordinates of the boundary kernels to arbitrary ℓ²
coefficients gives a continuous synthesis into the full Schwartz–Bergman space.
The pointwise continuity on the Hilbert side closes its graph. -/
private theorem spectralBoundary_hilbert_synthesis (K : ℂ → SchwartzMap ℝ ℂ)
    (hk : ∀ t : ℝ, Differentiable ℂ (fun z ↦ K z t))
    (hb : ∀ (A : ℝ) (p : ℕ), IsVonNBounded ℂ
      (range (fun z : {z : ℂ // |z.re| ≤ A} ↦ (((1+|z.val.im|)^p:ℝ):ℂ) • K z.val)))
    (e : SchwartzMap ℝ ℂ ≃L[ℂ] RapidDecaySequence 1) (k : ℕ) :
    let H := lp (fun _ : ℕ ↦ ℂ) 2
    let sourceSpace := SchwartzBergman (univ : Set ℝ)
    ∃ R : H →L[ℂ] sourceSpace,
      (∀ h z, (R h).val z = ∑' n : ℕ, h n * ((latticeWeight n ^ k:ℝ):ℂ) * e (K z) (latticeIndex n)) ∧
      ∀ (n : ℕ) z, (R (lp.single (E := fun _ : ℕ ↦ ℂ) 2 n (1:ℂ))).val z =
        ((latticeWeight n ^ k:ℝ):ℂ) * e (K z) (latticeIndex n) := by
  intro H sourceSpace
  obtain ⟨T,hT⟩ := spectralBoundary_synthesis_schwartzBergman K hk hb
  obtain ⟨L,hLc,hLs,hLn⟩ := spectralBoundary_weighted_pair k
  let pairing : StrongDual ℂ (RapidDecaySequence 1) →L[ℂ] StrongDual ℂ (SchwartzMap ℝ ℂ) :=
    ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ e.toContinuousLinearMap
  let R := (T.comp pairing.toLinearMap).comp L
  have val (x : H) (z : ℂ) : (R x).val z = L x (e (K z)) := hT _ z
  let ev (z : ℂ) := (entireJet z 0).comp schwartzBergmanEntireInclusion
  have he (z : ℂ) (f : sourceSpace) : ev z f = f.val z := by
    change entireJet z 0 (schwartzBergmanEntireInclusion f) = _
    rw [entireJet_apply,iteratedDeriv_zero,schwartzBergmanEntireInclusion_apply]
  have hg : (R.graph : Set (H × sourceSpace)) = ⋂ z : ℂ, {x : H × sourceSpace | L x.1 (e (K z)) = ev z x.2} := by
    ext x
    simp only [mem_iInter,mem_ofPred_eq,SetLike.mem_coe,LinearMap.mem_graph_iff]
    constructor
    · intro h z
      rw [he,h,val]
    · intro h
      apply Subtype.ext
      funext z
      exact ((h z).trans (he z _)).symm.trans (val _ _).symm
  have gc : IsClosed (R.graph : Set (H × sourceSpace)) := hg ▸ isClosed_iInter
    (fun z ↦ isClosed_eq ((hLc _).comp continuous_fst) ((ev z).continuous.comp continuous_snd))
  have hR : Continuous R := spectralBoundary_continuous_of_closedGraph (isFrechetTVS_of_banach H)
    (schwartzBergman_frechet univ isOpen_univ inferInstance univ_nonempty) R gc
  exact ⟨⟨R,hR⟩,fun h z ↦ (val h z).trans (hLs _ _),fun n z ↦ (val _ z).trans (hLn _ _)⟩

/-- A countable family of rapidly decreasing nonnegative rows admits a single positive
rapid majorant up to one constant per row. -/
private theorem spectralBoundary_rapidScale (p : ℕ → ℕ → ℝ)
    (hp : ∀ j k : ℕ, ∃ C : ℝ, ∀ n : ℕ, p j n * ((n:ℝ)+1)^k ≤ C) :
    ∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, c n * ((n:ℝ)+1)^k ≤ C) ∧
      (∀ j : ℕ, ∃ C : ℝ, ∀ n : ℕ, p j n ≤ C*c n) := by
  classical
  let W (n : ℕ) : ℝ := n+1
  have hW (n) : 1 ≤ W n := by dsimp [W]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have pos (n) : 0 < W n := zero_lt_one.trans_le (hW n)
  have eventual (j k : ℕ) : ∀ᶠ n in atTop, p j n * (W n)^k ≤ 1 := by
    obtain ⟨C,hC⟩ := hp j (k+1)
    obtain ⟨N,hN⟩ := exists_nat_ge C
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 : C ≤ W n := hN.trans (by dsimp [W]; exact_mod_cast (show N ≤ n + 1 by omega))
    have h2 := hC n
    change p j n * (W n)^(k+1) ≤ C at h2
    rw [pow_succ,←mul_assoc] at h2
    exact (le_of_mul_le_mul_right (by simpa only [one_mul] using h2.trans h1 : (p j n * W n ^ k) * W n ≤ 1 * W n) (pos n))
  let S (n : ℕ) := (Finset.range (n+1)).filter (fun k ↦ ∀ j ≤ k, p j n * (W n)^k ≤ 1)
  let H (n : ℕ) := (insert 0 (S n)).max' (Finset.insert_nonempty _ _)
  have good (k : ℕ) : ∀ᶠ n in atTop, k ∈ S n := by
    have hall : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (k+1), p j n * (W n)^k ≤ 1 :=
      (Finset.eventually_all _).mpr fun j _ ↦ eventual j k
    filter_upwards [eventually_ge_atTop k,hall] with n hn hn'
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),fun j hj ↦ hn' j (Finset.mem_range.mpr (by omega))⟩
  have large (k : ℕ) : ∀ᶠ n in atTop, k ≤ H n := (good k).mono fun n hn ↦
    Finset.le_max' _ _ (Finset.mem_insert_of_mem hn)
  have Hgood : ∀ᶠ n in atTop, H n ∈ S n := by
    filter_upwards [large 1] with n hn
    have hh : H n ∈ insert 0 (S n) := Finset.max'_mem _ _
    exact (Finset.mem_insert.mp hh).resolve_left (by omega)
  let c (n : ℕ) := ((W n)^(H n))⁻¹
  have cp (n) : 0 < c n := inv_pos.mpr (pow_pos (pos n) _)
  have global {f : ℕ → ℝ} (hf : ∀ᶠ n in atTop, f n ≤ 1) : ∃ C : ℝ, ∀ n, f n ≤ C := by
    rw [←Nat.cofinite_eq_atTop] at hf
    obtain ⟨C,hC⟩ := (isBoundedUnder_of_eventually_le hf).bddAbove_range_of_cofinite
    exact ⟨C,fun n ↦ hC (mem_range_self n)⟩
  refine ⟨c,cp,fun k ↦ global ?_,fun j ↦ ?_⟩
  · filter_upwards [large k] with n hn
    change ((W n)^(H n))⁻¹ * (W n)^k ≤ 1
    rw [inv_mul_eq_div, div_le_one (pow_pos (pos n) _)]
    exact pow_le_pow_right₀ (hW n) hn
  · obtain ⟨C,hC⟩ := global (f := fun n ↦ p j n * (W n)^(H n)) (by
      filter_upwards [Hgood,large j] with n hn hnj
      exact (Finset.mem_filter.mp hn).2 j hnj)
    refine ⟨C,fun n ↦ ?_⟩
    change p j n ≤ C * ((W n)^(H n))⁻¹
    rw [← div_eq_mul_inv,le_div_iff₀ (pow_pos (pos n) _)]
    exact hC n

private theorem spectralBoundary_gauge_image {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (φ : M ≃ₗ[ℂ] N) (s : Set M) (x : M) :
    gauge (φ '' s) (φ x) = gauge s x := by
  unfold gauge
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ ↦ ?_
  simp only [Set.mem_smul_set, Set.exists_mem_image]
  refine exists_congr fun y ↦ and_congr_right fun _ ↦ ?_
  rw [show r • φ y = φ (r • y) from (LinearMap.map_smul_of_tower φ.toLinearMap r y).symm]
  exact φ.injective.eq_iff

/-- The image of a Banach disc under an injective continuous linear map is a Banach disc:
the map restricts to a linear equivalence of the spans that preserves the gauges. -/
private theorem spectralBoundary_disc_image {Y Z : Type*}
    [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [PolynormableSpace ℂ Y] [T2Space Y]
    [AddCommGroup Z] [Module ℂ Z] [UniformSpace Z] [IsUniformAddGroup Z]
    [PolynormableSpace ℂ Z] [T2Space Z]
    {sourceSpace : Set Y} (hB : IsBanachDisc sourceSpace) (T : Y →L[ℂ] Z) (hT : Injective T) :
    IsBanachDisc (T '' sourceSpace) := by
  let S := Submodule.span ℂ sourceSpace
  let S' := Submodule.span ℂ (T '' sourceSpace)
  have hSS : S.map T.toLinearMap = S' := (Submodule.span_image T.toLinearMap).symm
  let φ : S ≃ₗ[ℂ] S' :=
    (Submodule.equivMapOfInjective T.toLinearMap hT S).trans (LinearEquiv.ofEq _ _ hSS)
  have himage : ((↑) ⁻¹' (T '' sourceSpace) : Set S') = φ '' ((↑) ⁻¹' sourceSpace : Set S) := by
    ext z
    constructor
    · rintro ⟨b, hb, hbz⟩
      exact ⟨⟨b, Submodule.subset_span hb⟩, hb, Subtype.ext hbz⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  have bB : Balanced ℂ ((↑) ⁻¹' (T '' sourceSpace) : Set S') :=
    himage ▸ hB.balanced.image φ.toLinearMap
  have cB : Convex ℝ ((↑) ⁻¹' (T '' sourceSpace) : Set S') :=
    himage ▸ hB.convex.linear_image (φ.toLinearMap.restrictScalars ℝ)
  have aB : Absorbent ℝ ((↑) ⁻¹' (T '' sourceSpace) : Set S') :=
    himage ▸ Absorbent.image_of_surjective (f := φ.toLinearMap.restrictScalars ℝ)
      φ.surjective hB.absorbent
  let p := gaugeSeminorm hB.balanced hB.convex hB.absorbent
  let p' := gaugeSeminorm bB cB aB
  have hnorm (z : S') : p' z = p (φ.symm z) := by
    change gauge _ z = gauge _ (φ.symm z)
    rw [himage, ← spectralBoundary_gauge_image φ, φ.apply_symm_apply]
  let ψ : WithLocalSeminorm p' → WithLocalSeminorm p := fun z ↦ (φ.symm (show S' from z) : S)
  have hψ : Isometry ψ := Isometry.of_dist_eq fun x y ↦ by
    rw [dist_eq_norm, dist_eq_norm]
    change p (φ.symm (show S' from x) - φ.symm (show S' from y)) =
      p' ((show S' from x) - (show S' from y))
    rw [← map_sub]
    exact (hnorm _).symm
  have hinj : Injective ψ := fun a b h ↦ φ.symm.injective h
  have hsurj : Surjective ψ := fun z ↦ ⟨(φ (show S from z) : S'), φ.symm_apply_apply _⟩
  have := hB.separated
  exact ⟨hB.bounded.image T, bB, cB, aB,
    T2Space.of_injective_continuous hinj hψ.continuous,
    (hψ.isUniformInducing.completeSpace_congr hsurj).mpr hB.complete⟩

/-- Every bounded sequence in a complete Hausdorff locally convex space lies in one Banach disc. The ℓ¹ synthesis construction is from the Chapter 7 biorthogonal certificate; factoring out its kernel removes the biorthogonality assumption. -/
theorem exists_isBanachDisc_of_isVonNBounded_range {I E : Type*} [DecidableEq I]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    (v : I → E) (bnd : IsVonNBounded ℂ (range v))
    :
    ∃ D : Set E, IsBanachDisc D ∧ ∀ i, v i ∈ D := by
  classical
  let X := lp (fun _ : I ↦ ℂ) 1
  let hp := PolynormableSpace.withSeminorms ℂ E
  have bounded_q (q : {q : Seminorm ℂ E // Continuous q}) :
      ∃ C > (0:ℝ), ∀ i, q.val (v i) ≤ C := by
    obtain ⟨C,hC,h⟩ := hp.isVonNBounded_iff_seminorm_bounded.mp bnd q
    exact ⟨C,hC,fun i ↦ (h _ (mem_range_self i)).le⟩
  have normsum (x : X) : HasSum (fun i ↦ ‖x i‖) ‖x‖ := by
    simpa using (lp.hasSum_norm (p := (1:ℝ≥0∞)) (by simp) x)
  have hterms (x : X) : Summable (fun i ↦ x i • v i) := by
    apply summable_iff_cauchySeq_finset.mpr
    apply cauchySeq_finset_iff_sum_vanishing.mpr
    intro region hU
    obtain ⟨p,hp0,hpU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hU
    obtain ⟨C,hC,hh⟩ := bounded_q ⟨p,hp0⟩
    have hmajor := (normsum x).summable.mul_left C
    obtain ⟨s,hs⟩ := cauchySeq_finset_iff_sum_vanishing.mp
      (summable_iff_cauchySeq_finset.mp hmajor) (Iio 1) (Iio_mem_nhds zero_lt_one)
    refine ⟨s,fun u hu ↦ hpU (p.mem_ball_zero.mpr (lt_of_le_of_lt ?_ (hs u hu)))⟩
    calc
      p (∑ i ∈ u, x i • v i) ≤ ∑ i ∈ u, p (x i • v i) :=
        Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ ↦ by
        rw [map_smul_eq_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hh i) (norm_nonneg _)
  let A : X →ₗ[ℂ] E :=
    { toFun := fun x ↦ ∑' i, x i • v i
      map_add' := fun x y ↦ by
        simpa [add_smul] using (hterms x).tsum_add (hterms y)
      map_smul' := fun c x ↦ by
        change (∑' i, (c * x i) • v i) = c • _
        simpa [smul_smul] using (hterms x).tsum_const_smul c }
  have cont : Continuous A := by
    apply hp.continuous_of_continuous_comp A
    intro q
    obtain ⟨C,hC,h⟩ := bounded_q q
    apply Seminorm.continuous' (r := C+1)
    refine mem_of_superset (Metric.ball_mem_nhds (0:X) one_pos) fun x hx ↦ ?_
    rw [Metric.mem_ball,dist_zero_right] at hx
    have hlimit := q.property.continuousAt.tendsto.comp (hterms x).hasSum
    have hmajor := ((normsum x).mul_left C)
    have hbound : q.val (A x) ≤ C * ‖x‖ :=
      le_of_tendsto_of_tendsto' hlimit hmajor (fun s ↦ by
        change q.val (∑ i ∈ s, x i • v i) ≤ ∑ i ∈ s, C * ‖x i‖
        refine (Finset.le_sum_of_subadditive q.val (map_zero q.val).le (map_add_le_add q.val) _ _).trans ?_
        apply Finset.sum_le_sum
        intro i _
        rw [map_smul_eq_mul,mul_comm]
        exact mul_le_mul_of_nonneg_right (h i) (norm_nonneg _))
    apply (q.val.comp A).mem_closedBall_zero.mpr
    change q.val (A x) ≤ C+1
    nlinarith
  let S : X →L[ℂ] E := ⟨A,cont⟩
  let K := S.ker
  let : IsClosed (K : Set X) := S.isClosed_ker
  let L₀ := K.liftQ S.toLinearMap (le_refl K)
  let L : (X ⧸ K) →L[ℂ] E := ⟨L₀, (Submodule.isQuotientMap_mkQ K).continuous_iff.mpr S.continuous⟩
  have inj : Injective L := LinearMap.ker_eq_bot.mp (K.ker_liftQ_eq_bot S.toLinearMap le_rfl le_rfl)
  refine ⟨L '' Metric.closedBall (0:X ⧸ K) 1, spectralBoundary_disc_image isBanachDisc_closedUnitBall L inj,?_⟩
  intro i
  let e : X := lp.single (E := fun _ : I ↦ ℂ) 1 i (1:ℂ)
  refine ⟨K.mkQ e,?_,?_⟩
  · rw [Metric.mem_closedBall,dist_zero_right]
    apply (Submodule.Quotient.norm_mk_le K e).trans
    dsimp only [e]
    rw [lp.norm_single (by norm_num), norm_one]
  · change (∑' j : I, lp.single (E := fun _ : I ↦ ℂ) 1 i (1:ℂ) j • v j) = v i
    simpa [lp.single_apply] using
      (tsum_eq_single i (f := fun j : I ↦ lp.single (E := fun _ : I ↦ ℂ) 1 i (1:ℂ) j • v j)
        (fun j hj ↦ by simp [lp.single_apply,hj]))

/-- A Hilbert-space boundary extension descends through a quotient by first choosing the
representative perpendicular to the kernel of the synthesis. -/
private theorem spectralBoundary_lift {sourceSpace H E : Type*}
    [AddCommGroup sourceSpace] [Module ℂ sourceSpace] [TopologicalSpace sourceSpace]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
    (q : sourceSpace →L[ℂ] E) (hq : Topology.IsQuotientMap q)
    (boundary : sourceSpace →L[ℂ] H) (synthesis : H →L[ℂ] E) (T : E →L[ℂ] E)
    (hT : ∀ x, synthesis (boundary x) = T (q x)) :
    ∃ lift : E →L[ℂ] H, synthesis.comp lift = T := by
  let K := synthesis.ker
  let : CompleteSpace K := synthesis.isClosed_ker.completeSpace_coe
  let region := (ContinuousLinearMap.id ℂ H - K.starProjection).comp boundary
  have correction (x : sourceSpace) : synthesis (region x) = T (q x) := by
    change synthesis (boundary x - K.starProjection (boundary x)) = _
    rw [map_sub, show synthesis (K.starProjection (boundary x)) = 0 from K.starProjection_apply_mem _, sub_zero, hT]
  have hker (x : sourceSpace) (hx : q x = 0) : region x = 0 := by
    change boundary x - K.starProjection (boundary x) = 0
    rw [K.starProjection_eq_self_iff.mpr (show boundary x ∈ K by
      change synthesis (boundary x) = 0
      rw [hT,hx,map_zero]), sub_self]
  obtain ⟨s,hs⟩ := q.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq.surjective)
  have right (y : E) : q (s y) = y := DFunLike.congr_fun hs y
  let L := region.toLinearMap.comp s
  have heq (x : sourceSpace) : L (q x) = region x := by
    have h := hker (s (q x) - x) (by rw [map_sub,right,sub_self])
    simpa only [L,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,map_sub,sub_eq_zero] using h
  have hcont : Continuous L := hq.continuous_iff.mpr (by simpa only [Function.comp_def,heq] using region.continuous)
  refine ⟨⟨L,hcont⟩,ContinuousLinearMap.ext fun y ↦ ?_⟩
  obtain ⟨x,rfl⟩ := hq.surjective y
  change synthesis (L (q x)) = _
  rw [heq,correction]

/-- A single rapid presentation of boundary synthesis gives a single rapid presentation
on the quotient with exactly the same coefficients, vectors, and Banach disc. -/
private theorem spectralBoundary_strong_of_synthesis {sourceSpace H E : Type*}
    [AddCommGroup sourceSpace] [Module ℂ sourceSpace] [TopologicalSpace sourceSpace]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [T2Space E]
    (q : sourceSpace →L[ℂ] E) (hq : Topology.IsQuotientMap q)
    (boundary : sourceSpace →L[ℂ] H) (synthesis : H →L[ℂ] E) (T : E →L[ℂ] E)
    (hT : ∀ x, synthesis (boundary x) = T (q x))
    (r : NuclearPresentation synthesis)
    (rapid : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖r.coeff n‖ * ((n:ℝ)+1)^k ≤ C) :
    IsStronglyNuclearOperator T := by
  obtain ⟨L,rfl⟩ := spectralBoundary_lift q hq boundary synthesis T hT
  let r' : NuclearPresentation (synthesis.comp L) :=
    { coeff := r.coeff, functional := fun n ↦ (r.functional n).comp L
      disc := r.disc, isBanachDisc := r.isBanachDisc, vector := r.vector,
      vector_mem := r.vector_mem, summable_coeff := r.summable_coeff,
      equicontinuous := fun region hU ↦ by
        have h := (L.continuous.tendsto' 0 0 (map_zero L)).eventually (r.equicontinuous region hU)
        simpa only [ContinuousLinearMap.comp_apply, map_zero] using h
      hasSum := fun x ↦ r.hasSum (L x) }
  exact ⟨r',rapid⟩

/-- A smoothing synthesis operator from a separable complex Hilbert space into a
complete countably seminormed space has a single rapid nuclear presentation if its
orthonormal columns decrease rapidly in every generating seminorm. -/
private theorem spectralBoundary_presentation_of_rapid_columns {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    (p : ℕ → Seminorm ℂ E) (hp : WithSeminorms p)
    (b : HilbertBasis ℕ ℂ H) (R : H →L[ℂ] E)
    (h : ∀ j k : ℕ, ∃ C : ℝ, ∀ n : ℕ, p j (R (b n)) * ((n:ℝ)+1)^k ≤ C) :
    ∃ r : NuclearPresentation R, ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      ‖r.coeff n‖ * ((n:ℝ)+1)^k ≤ C := by
  obtain ⟨c,hc,hr,hd⟩ := spectralBoundary_rapidScale (fun j n ↦ p j (R (b n))) h
  let v (n : ℕ) := ((c n : ℂ)⁻¹) • R (b n)
  have bv : IsVonNBounded ℂ (range v) := by
    apply hp.isVonNBounded_iff_seminorm_bddAbove.mpr
    intro j
    obtain ⟨C,hC⟩ := hd j
    refine ⟨C,?_⟩
    rintro _ ⟨_,⟨n,rfl⟩,rfl⟩
    change p j ((c n : ℂ)⁻¹ • R (b n)) ≤ C
    rw [map_smul_eq_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hc n),inv_mul_eq_div]
    exact (div_le_iff₀ (hc n)).mpr (hC n)
  obtain ⟨D,hD,hv⟩ := exists_isBanachDisc_of_isVonNBounded_range v bv
  let L (n : ℕ) : H →L[ℂ] ℂ := innerSL ℂ (b n)
  have hL : EquicontinuousAt (fun n x ↦ L n x) 0 := by
    apply Metric.equicontinuousAt_of_continuity_modulus (fun x : H ↦ ‖x‖)
      (by simpa using (continuous_norm : Continuous (norm : H → ℝ)).tendsto 0)
    refine Eventually.of_forall fun x n ↦ ?_
    rw [map_zero,dist_zero_left]
    exact (norm_inner_le_norm _ _).trans_eq (by simp [b.orthonormal.norm_eq_one n])
  have hs : Summable c := by
    obtain ⟨C,hC⟩ := hr 2
    have hsum : Summable (fun n : ℕ ↦ 1 / ((n:ℝ)+1)^2) := by
      simpa only [Real.rpow_two,sq_abs] using (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    refine (hsum.mul_left C).of_norm_bounded fun n ↦ ?_
    rw [Real.norm_eq_abs,abs_of_pos (hc n),mul_one_div]
    exact (le_div_iff₀ (by positivity)).2 (hC n)
  let r : NuclearPresentation R :=
    { coeff := fun n ↦ (c n:ℂ), functional := L, disc := D, isBanachDisc := hD
      vector := fun n ↦ ⟨v n,Submodule.subset_span (hv n)⟩
      vector_mem := hv
      summable_coeff := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hc _)] using hs
      equicontinuous := hL
      hasSum := fun x ↦ ((b.hasSum_repr x).mapL R).congr_fun fun n ↦ by
        change ((c n:ℂ) * L n x) • v n = (R ((b.repr x n) • b n))
        rw [map_smul,HilbertBasis.repr_apply_apply,show L n x = inner ℂ (b n) x from rfl]
        dsimp only [v]
        rw [smul_smul]
        congr 1
        field_simp [Complex.ofReal_ne_zero.mpr (hc n).ne'] }
  refine ⟨r,fun k ↦ ?_⟩
  obtain ⟨C,hC⟩ := hr k
  exact ⟨C,fun n ↦ by simpa only [r,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hc n)] using hC n⟩

/-- Every polynomially reweighted fixed-line synthesis has a single rapid
presentation after projection to any complete countably-seminormed space. -/
private theorem spectralBoundary_contour_presentation {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    (p : ℕ → Seminorm ℂ E) (hp : WithSeminorms p)
    (K : ℂ → SchwartzMap ℝ ℂ)
    (hk : ∀ t : ℝ, Differentiable ℂ (fun z ↦ K z t))
    (hb : ∀ (A : ℝ) (s : ℕ), IsVonNBounded ℂ
      (range (fun z : {z : ℂ // |z.re| ≤ A} ↦ (((1+|z.val.im|)^s:ℝ):ℂ) • K z.val)))
    (e : SchwartzMap ℝ ℂ ≃L[ℂ] RapidDecaySequence 1) (k : ℕ)
    (q : SchwartzBergman (univ : Set ℝ) →L[ℂ] E) :
    let H := lp (fun _ : ℕ ↦ ℂ) 2
    let sourceSpace := SchwartzBergman (univ : Set ℝ)
    ∃ R : H →L[ℂ] sourceSpace,
      (∀ h z, (R h).val z = ∑' n : ℕ, h n * ((latticeWeight n ^ k:ℝ):ℂ) * e (K z) (latticeIndex n)) ∧
      ∃ r : NuclearPresentation (q.comp R), ∀ j : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖r.coeff n‖*((n:ℝ)+1)^j ≤ C := by
  intro H sourceSpace
  choose R hR hunit using spectralBoundary_hilbert_synthesis K hk hb e
  refine ⟨R k,hR k,?_⟩
  let basis : HilbertBasis ℕ ℂ H := ⟨LinearIsometryEquiv.refl ℂ H⟩
  let u (n : ℕ) : H := lp.single 2 n 1
  have bval (n : ℕ) : basis n = u n := by rw [← basis.repr_symm_single]; rfl
  have un (n : ℕ) : u n ∈ Metric.closedBall (0:H) 1 := by
    rw [Metric.mem_closedBall,dist_zero_right,← bval, basis.orthonormal.norm_eq_one n]
  apply spectralBoundary_presentation_of_rapid_columns p hp basis (q.comp (R k))
  intro i j
  let T := q.comp (R (k+j))
  have hbd : IsVonNBounded ℂ (T '' Metric.closedBall (0:H) 1) :=
    (NormedSpace.isVonNBounded_closedBall ℂ H 1).image T
  obtain ⟨C,hC⟩ := hp.isVonNBounded_iff_seminorm_bddAbove.mp hbd i
  refine ⟨(2:ℝ)^j*C,fun n ↦ ?_⟩
  have hw : 0 ≤ latticeWeight n := zero_le_one.trans (latticeWeight_bounds n).1
  have hsc : R (k+j) (u n) = ((latticeWeight n ^ j : ℝ):ℂ) • R k (u n) := by
    apply Subtype.ext
    funext z
    change (R (k+j) (u n)).val z = ((latticeWeight n ^ j:ℝ):ℂ) * (R k (u n)).val z
    dsimp only [u]
    rw [hunit,hunit,pow_add,Complex.ofReal_mul]
    ring
  have bound := hC (mem_image_of_mem _ (mem_image_of_mem T (un n)))
  change p i (q ((R (k+j)) (u n))) ≤ C at bound
  rw [hsc,map_smul,map_smul_eq_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hw j)] at bound
  rw [bval]
  change p i (q (R k (u n))) * ((n:ℝ)+1)^j ≤ _
  calc
    _ ≤ p i (q (R k (u n))) * (2*latticeWeight n)^j := by
      gcongr; exact (latticeWeight_bounds n).2.2
    _ = 2^j * ((latticeWeight n)^j * p i (q (R k (u n)))) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left bound (by positivity)

open MeasureTheory Complex

/-- Gaussian regularization of the Cauchy kernel with its moving pole removed. -/
private def spectralBoundaryKernel (G : ℂ → ℂ) (w z : ℂ) : ℂ :=
  Complex.exp ((z-w)^2) * dslope G w z / G w

private theorem spectralBoundaryKernel_entire {G : ℂ → ℂ} (hG : Differentiable ℂ G) (w : ℂ) :
    Differentiable ℂ (spectralBoundaryKernel G w) := by
  apply Differentiable.div_const
  apply Differentiable.mul
  · fun_prop
  · exact fun z ↦ ((hG.analyticAt z).dslope w).differentiableAt

private theorem spectralBoundaryKernel_offPole {G : ℂ → ℂ} {w z : ℂ} (hz : z ≠ w) (hw : G w ≠ 0) :
    spectralBoundaryKernel G w z =
      Complex.exp ((z-w)^2) / (w-z) * (1 - G z / G w) := by
  simp only [spectralBoundaryKernel, dslope_of_ne _ hz,slope,smul_eq_mul,vsub_eq_sub]
  field_simp [sub_ne_zero.mpr hz,sub_ne_zero.mpr hz.symm,hw]
  ring

private theorem spectralBoundary_dslope_norm {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (A C : ℝ) (n : ℕ) (hC : 0 ≤ C)
    (hder : ∀ x : ℂ, |x.re| ≤ A → ‖deriv G x‖ ≤ C * (1+|x.im|)^n)
    (w z : ℂ) (hw : |w.re| ≤ A) (hz : |z.re| ≤ A) :
    ‖dslope G w z‖ ≤ C * (1+|w.im|+|z.im-w.im|)^n := by
  let b := |w.im| + |z.im-w.im|
  have hb : |z.im| ≤ b := by
    calc
      |z.im| = |(z.im-w.im)+w.im| := by congr 1; ring
      _ ≤ |z.im-w.im| + |w.im| := abs_add_le _ _
      _ = b := add_comm _ _
  have hw' : |w.im| ≤ b := le_add_of_nonneg_right (abs_nonneg _)
  let S := {x : ℂ | x.re ∈ Icc (-A) A ∧ x.im ∈ Icc (-b) b}
  have cv : Convex ℝ S := ((convex_halfSpace_re_ge (-A)).inter (convex_halfSpace_re_le A)).inter
    ((convex_halfSpace_im_ge (-b)).inter (convex_halfSpace_im_le b))
  have hbd (x : ℂ) (hx : x ∈ S) : ‖deriv G x‖ ≤ C * (1+b)^n := by
    refine (hder x (abs_le.mpr hx.1)).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add_right (abs_le.mpr hx.2) 1) n) hC
  have zm : z ∈ S := ⟨abs_le.mp hz,abs_le.mp hb⟩
  have wm : w ∈ S := ⟨abs_le.mp hw,abs_le.mp hw'⟩
  have goal : ‖dslope G w z‖ ≤ C * (1+b)^n := by
    by_cases e : z = w
    · subst z; simpa only [dslope_same] using hbd w wm
    · rw [dslope_of_ne _ e,slope,smul_eq_mul,norm_mul,norm_inv,inv_mul_eq_div]
      apply (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr e))).mpr
      exact cv.norm_image_sub_le_of_norm_deriv_le (fun x _ ↦ hG x) hbd wm zm
  simpa only [b,add_assoc] using goal

private theorem spectralBoundary_gaussian_abs_pow (m : ℕ) (u : ℝ) :
    (1 + |u|)^m * Real.exp (-(u^2)) ≤ Real.exp ((m:ℝ)^2) := by
  have h := Real.add_one_le_exp |u|
  have hp : (1+|u|)^m ≤ Real.exp ((m:ℝ)*|u|) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc
    _ ≤ Real.exp ((m:ℝ)*|u|) * Real.exp (-(u^2)) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp ((m:ℝ)*|u| - u^2) := by rw [←Real.exp_add]; rfl
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ((m:ℝ) - |u|),sq_abs u,sq_nonneg u])

/-- The entire interpolation vector on a vertical contour grows at most polynomially
in the contour height, for each fixed output Schwartz–Bergman seminorm. The same bound
applies uniformly on any narrow complex tube where the reciprocal bound holds. -/
private theorem spectralBoundaryKernel_strip {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (A C D : ℝ) (n b p : ℕ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hder : ∀ x : ℂ, |x.re| ≤ A → ‖deriv G x‖ ≤ C * (1+|x.im|)^n) :
    ∃ K : ℝ, ∀ w z : ℂ, |w.re| ≤ A → |z.re| ≤ A →
      ‖(G w)⁻¹‖ ≤ D*(1+|w.im|)^b →
      (1+|z.im|)^p * ‖spectralBoundaryKernel G w z‖ ≤ K * (1+|w.im|)^(p+n+b) := by
  let m := p+n
  refine ⟨Real.exp ((2*A)^2) * C * D * Real.exp ((m:ℝ)^2), ?_⟩
  intro w z hw hz hi
  let u := z.im-w.im
  let region := 1+|u|
  let targetSet := 1+|w.im|
  have hU : 0 ≤ region := by dsimp [region]; positivity
  have hV : 0 ≤ targetSet := by dsimp [targetSet]; positivity
  have ht : 1+|w.im|+|u| ≤ targetSet*region := by
    dsimp [targetSet,region]; nlinarith [mul_nonneg (abs_nonneg w.im) (abs_nonneg u)]
  have hy : 1+|z.im| ≤ targetSet*region := by
    have h := abs_add_le u w.im
    rw [show u + w.im = z.im by dsimp [u];ring] at h
    linarith
  have hr : |z.re-w.re| ≤ 2*A := (abs_sub _ _).trans (by linarith)
  have hs : (z.re-w.re)^2 ≤ (2*A)^2 := by
    nlinarith [sq_abs (z.re-w.re),abs_nonneg (z.re-w.re),mul_nonneg (sub_nonneg.mpr hr) (add_nonneg (hr.trans' (abs_nonneg _)) (abs_nonneg (z.re-w.re)))]
  have hg : ‖Complex.exp ((z-w)^2)‖ ≤ Real.exp ((2*A)^2) * Real.exp (-(u^2)) := by
    rw [Complex.norm_exp,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [pow_two,Complex.mul_re,Complex.sub_re,Complex.sub_im,u]
    nlinarith
  have hdiff : ‖dslope G w z‖ ≤ C*(targetSet*region)^n := by
    refine (spectralBoundary_dslope_norm hG A C n hC hder w z hw hz).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht _) hC
  change _ ≤ _ * targetSet^(p+n+b)
  rw [spectralBoundaryKernel,div_eq_mul_inv,norm_mul,norm_mul]
  calc
    _ ≤ (targetSet*region)^p * (Real.exp ((2*A)^2) * Real.exp (-(u^2)) * (C*(targetSet*region)^n) * (D*targetSet^b)) := by
      gcongr
    _ = (Real.exp ((2*A)^2)*C*D*targetSet^(p+n+b)) * (region^m * Real.exp (-(u^2))) := by
      simp only [m,pow_add,mul_pow]; ring
    _ ≤ (Real.exp ((2*A)^2)*C*D*targetSet^(p+n+b)) * Real.exp ((m:ℝ)^2) := by
      apply mul_le_mul_of_nonneg_left (spectralBoundary_gaussian_abs_pow m u)
      positivity
    _ = _ := by ring

/-- The moving, regularized Cauchy vector is holomorphic in its integration parameter
where the generator is nonzero, including at the removable diagonal. -/
private theorem spectralBoundaryKernel_moving {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (z w : ℂ) (hw : G w ≠ 0) :
    DifferentiableAt ℂ (fun t ↦ spectralBoundaryKernel G t z) w := by
  have hswap (t : ℂ) : dslope G t z = dslope G z t := by
    by_cases ht : t=z
    · rw [ht]
    · rw [dslope_of_ne _ (Ne.symm ht),dslope_of_ne _ ht,slope_comm]
  unfold spectralBoundaryKernel
  simp_rw [hswap]
  have he : DifferentiableAt ℂ (fun t : ℂ ↦ Complex.exp ((z-t)^2)) w := by fun_prop
  exact (he.mul ((hG.analyticAt w).dslope z).differentiableAt).div (hG w) hw

/-- The kernel multiplied by a test Mellin transform is uniformly Schwartz in the
boundary parameter, including all its derivatives, in each output strip seminorm. -/
private theorem spectralBoundaryKernel_schwartz {G M : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hM : Differentiable ℂ M) (A C D σ : ℝ) (n b : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hσ : |σ|+1 ≤ A)
    (hder : ∀ x : ℂ, |x.re| ≤ A → ‖deriv G x‖ ≤ C*(1+|x.im|)^n)
    (hinv : ∀ w : ℂ, |w.re-σ| ≤ 1 → G w ≠ 0 ∧ ‖(G w)⁻¹‖ ≤ D*(1+|w.im|)^b)
    (hrapid : ∀ k : ℕ, ∃ E > (0:ℝ), ∀ w : ℂ, |w.re-σ| ≤ 1 → (1+|w.im|)^k*‖M w‖ ≤ E)
    (p k j : ℕ) : ∃ sourceSpace : ℝ, ∀ w z : ℂ, w.re = σ → |z.re| ≤ A →
      (1+|z.im|)^p * (1+|w.im|)^k *
        ‖iteratedDeriv j (fun v ↦ M v * spectralBoundaryKernel G v z) w‖ ≤ sourceSpace := by
  obtain ⟨K,hK⟩ := spectralBoundaryKernel_strip hG A C D n b p hC hD hder
  let K' := max 0 K
  have Kp : 0 ≤ K' := le_max_left _ _
  let m := p+n+b
  obtain ⟨E,hE,hEM⟩ := hrapid (m+k)
  refine ⟨j.factorial * (2^k * K' * E),?_⟩
  intro w z hw hz
  let Z := (1+|z.im|)^p
  let W := (1+|w.im|)^k
  let H : ℂ := ((Z*W:ℝ):ℂ)
  have hh : ‖H‖ = Z*W := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    positivity
  have tube (v : ℂ) (hv : v ∈ Metric.closedBall w 1) :
      |v.re - σ| ≤ 1 ∧ |v.re| ≤ A ∧ 1+|w.im| ≤ 2*(1+|v.im|) := by
    have hdist := mem_closedBall_iff_norm.mp hv
    have hre := (Complex.abs_re_le_norm (v-w)).trans hdist
    have him := (Complex.abs_im_le_norm (v-w)).trans hdist
    rw [Complex.sub_re,hw] at hre
    rw [Complex.sub_im] at him
    refine ⟨hre,?_,?_⟩
    · have t := abs_add_le (v.re-σ) σ
      rw [sub_add_cancel] at t
      linarith
    · have t := abs_sub v.im (v.im-w.im)
      rw [sub_sub_cancel] at t
      linarith [abs_nonneg v.im]
  let F (v : ℂ) := M v * spectralBoundaryKernel G v z
  have ha (v : ℂ) (hv : v ∈ Metric.closedBall w 1) : DifferentiableAt ℂ F v :=
    (hM v).mul (spectralBoundaryKernel_moving hG z v (hinv v (tube v hv).1).1)
  have hd : DiffContOnCl ℂ (fun v ↦ H * F v) (Metric.ball w 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball w one_ne_zero]
    exact fun v hv ↦ ((ha v hv).const_mul H).differentiableWithinAt
  have hbound (v : ℂ) (hv : v ∈ Metric.sphere w 1) : ‖H * F v‖ ≤ 2^k*K'*E := by
    obtain ⟨hhv,hva,hvi⟩ := tube v (Metric.sphere_subset_closedBall hv)
    let h := 1+|v.im|
    have hp : 0 ≤ h := by dsimp [h]; positivity
    have hKer : Z * ‖spectralBoundaryKernel G v z‖ ≤ K' * h^m :=
      (hK v z hva hz (hinv v hhv).2).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hp m))
    have hW : W ≤ 2^k * h^k := by simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hvi k
    rw [norm_mul,hh]
    change Z*W*(‖M v * spectralBoundaryKernel G v z‖) ≤ _
    rw [norm_mul]
    calc
      _ = W * (Z * ‖spectralBoundaryKernel G v z‖) * ‖M v‖ := by ring
      _ ≤ (2^k * h^k) * (K'*h^m) * ‖M v‖ := by gcongr
      _ = (2^k*K') * (h^(m+k)*‖M v‖) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hEM v hhv) (by positivity)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j one_pos hd hbound
  rw [iteratedDeriv_const_mul_field,norm_mul,hh,one_pow,div_one] at h
  exact h

local notation "linePoint" => (fun (x y : ℝ) ↦ (x : ℂ) + y * Complex.I)
private theorem spectralContour_hasDerivAt_vertical_iterate {I : Set ℝ} (hI : IsOpen I) (a : I)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' I)) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Complex.I ^ n * iteratedDeriv n f (linePoint a y))
      (Complex.I ^ (n+1) * iteratedDeriv (n+1) f (linePoint a x)) x := by
  have hU := hI.preimage Complex.continuous_re
  have han : ∀ m, AnalyticOnNhd ℂ (iteratedDeriv m f) (Complex.re ⁻¹' I) := by
    intro m
    induction m with
    | zero => simpa using hf.analyticOnNhd hU
    | succ m ih => rw [iteratedDeriv_succ]; exact fun z hz ↦ (ih z hz).deriv
  have hd := (han n _ (show linePoint a x ∈ Complex.re ⁻¹' I by simp)).differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun w : ℂ ↦ (a.val : ℂ) + w * Complex.I) Complex.I (x : ℂ) := by
    simpa using (((hasDerivAt_id (x : ℂ)).mul_const Complex.I).const_add (a.val : ℂ))
  have h := ((hd.comp (x : ℂ) hline).comp_ofReal).const_mul (Complex.I ^ n)
  simpa only [Function.comp_apply, iteratedDeriv_succ, pow_succ, mul_left_comm,
    mul_assoc, mul_comm (deriv _ _)] using h

private theorem spectralContour_iteratedDeriv_vertical {I : Set ℝ} (hI : IsOpen I) (a : I)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' I)) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ ↦ f (linePoint a y)) =
      fun y ↦ Complex.I ^ n * iteratedDeriv n f (linePoint a y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (spectralContour_hasDerivAt_vertical_iterate hI a hf n x).deriv

/-- A family holomorphic on a neighborhood of a whole vertical line with uniform
Schwartz bounds for all holomorphic derivatives on that line is a bounded family
of real Schwartz functions after restriction. -/
private theorem spectralBoundary_schwartz_line_family {X : Type*} (F : X → ℂ → ℂ) (σ : ℝ)
    (hol : ∀ i, DifferentiableOn ℂ (F i) (Complex.re ⁻¹' Ioo (σ-1) (σ+1)))
    (bounds : ∀ k j : ℕ, ∃ C : ℝ, ∀ i (t : ℝ),
      (1+|t|)^k * ‖iteratedDeriv j (F i) (linePoint σ t)‖ ≤ C) :
    ∃ f : X → SchwartzMap ℝ ℂ, (∀ i t, f i t = F i (linePoint σ t)) ∧
      Bornology.IsVonNBounded ℂ (range f) := by
  let s : Ioo (σ-1) (σ+1) := ⟨σ,by constructor <;> linarith⟩
  have hdec (k j : ℕ) : ∃ C : ℝ, ∀ i (t : ℝ),
      ‖t‖^k * ‖iteratedFDeriv ℝ j (fun t : ℝ ↦ F i (linePoint σ t)) t‖ ≤ C := by
    obtain ⟨C,hC⟩ := bounds k j
    refine ⟨C,fun i t ↦ ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, show σ = s.val from rfl,
      spectralContour_iteratedDeriv_vertical isOpen_Ioo s (hol i),norm_mul,norm_pow,Complex.norm_I,one_pow,one_mul]
    apply le_trans _ (hC i t)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (by rw [Real.norm_eq_abs]; linarith) _) (norm_nonneg _)
  let f (i : X) : SchwartzMap ℝ ℂ :=
    { toFun := fun t ↦ F i (linePoint σ t)
      smooth' := by
        apply contDiff_of_differentiable_iteratedDeriv
        intro j _ t
        rw [show σ = s.val from rfl,spectralContour_iteratedDeriv_vertical isOpen_Ioo s (hol i)]
        exact (spectralContour_hasDerivAt_vertical_iterate isOpen_Ioo s (hol i) j t).differentiableAt
      decay' := fun k j ↦ ⟨(hdec k j).choose,(hdec k j).choose_spec i⟩ }
  refine ⟨f,fun i t ↦ rfl,?_⟩
  apply (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bddAbove.mpr
  rintro ⟨k,j⟩
  obtain ⟨C,hC⟩ := hdec k j
  refine ⟨max 0 C,?_⟩
  rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
  exact SchwartzMap.seminorm_le_bound ℂ k j (f i) (le_max_left _ _)
    (fun x ↦ (hC i x).trans (le_max_right _ _))

/-- The weighted boundary kernels form a bounded family in the scalar Schwartz space.
The bound covers all their boundary derivatives simultaneously on the same contour. -/
private theorem spectralBoundary_schwartz_vectors {G M : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hM : Differentiable ℂ M) (A C D σ : ℝ) (n b : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hσ : |σ|+1 ≤ A)
    (hder : ∀ x : ℂ, |x.re| ≤ A → ‖deriv G x‖ ≤ C*(1+|x.im|)^n)
    (hinv : ∀ w : ℂ, |w.re-σ| ≤ 1 → G w ≠ 0 ∧ ‖(G w)⁻¹‖ ≤ D*(1+|w.im|)^b)
    (hrapid : ∀ k : ℕ, ∃ E > (0:ℝ), ∀ w : ℂ, |w.re-σ| ≤ 1 → (1+|w.im|)^k*‖M w‖ ≤ E)
    (p : ℕ) :
    ∃ f : {z : ℂ // |z.re| ≤ A} → SchwartzMap ℝ ℂ,
      (∀ z t, f z t = (((1+|z.val.im|)^p:ℝ):ℂ) * (M (linePoint σ t) * spectralBoundaryKernel G (linePoint σ t) z.val)) ∧
      Bornology.IsVonNBounded ℂ (range f) := by
  apply spectralBoundary_schwartz_line_family
    (fun z : {z : ℂ // |z.re| ≤ A} ↦ fun w ↦ (((1+|z.val.im|)^p:ℝ):ℂ) * (M w * spectralBoundaryKernel G w z.val)) σ
  · intro z w hw
    have h : |w.re-σ| ≤ 1 := abs_le.mpr ⟨by linarith [hw.1],by linarith [hw.2]⟩
    exact (((hM w).mul (spectralBoundaryKernel_moving hG z.val w (hinv w h).1)).const_mul _).differentiableWithinAt
  · intro k j
    obtain ⟨sourceSpace,hB⟩ := spectralBoundaryKernel_schwartz hG hM A C D σ n b hC hD hσ hder hinv hrapid p k j
    refine ⟨sourceSpace,fun z t ↦ ?_⟩
    have h := hB (linePoint σ t) z.val (by simp) z.property
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] at h
    rw [iteratedDeriv_const_mul_field,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (1+|z.val.im|)^p by positivity)]
    simpa only [mul_assoc,mul_left_comm] using h

/-- The entire comparison generator gives a globally defined Schwartz-valued
kernel. Every polynomially weighted output strip is bounded in the real Schwartz space. -/
private theorem spectralBoundary_global_kernel {G M : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hM : Differentiable ℂ M) (σ : ℝ)
    (hd : ∀ A : ℝ, ∃ n : ℕ, ∃ C > (0:ℝ), ∀ x : ℂ, |x.re| ≤ A →
      ‖deriv G x‖ ≤ C*(1+|x.im|)^n)
    (hinv : ∃ b : ℕ, ∃ D > (0:ℝ), ∀ w : ℂ, |w.re-σ| ≤ 1 → G w ≠ 0 ∧ ‖(G w)⁻¹‖ ≤ D*(1+|w.im|)^b)
    (hm : ∀ k : ℕ, ∃ E > (0:ℝ), ∀ w : ℂ, |w.re-σ| ≤ 1 → (1+|w.im|)^k*‖M w‖ ≤ E) :
    ∃ K : ℂ → SchwartzMap ℝ ℂ,
      (∀ z t, K z t = M (linePoint σ t) * spectralBoundaryKernel G (linePoint σ t) z) ∧
      (∀ t : ℝ, Differentiable ℂ (fun z ↦ K z t)) ∧
      ∀ (A : ℝ) (p : ℕ), Bornology.IsVonNBounded ℂ
        (range (fun z : {z : ℂ // |z.re| ≤ A} ↦ (((1+|z.val.im|)^p:ℝ):ℂ) • K z.val)) := by
  obtain ⟨b,D,hD,hI⟩ := hinv
  have localFamily (A : ℝ) (p : ℕ) :
      ∃ f : {z : ℂ // |z.re| ≤ A} → SchwartzMap ℝ ℂ,
        (∀ z t, f z t = (((1+|z.val.im|)^p:ℝ):ℂ) * (M (linePoint σ t) * spectralBoundaryKernel G (linePoint σ t) z.val)) ∧
        Bornology.IsVonNBounded ℂ (range f) := by
    let A' := max (|σ|+1) A
    obtain ⟨n,C,hC,h⟩ := hd A'
    obtain ⟨f,hf,hb⟩ := spectralBoundary_schwartz_vectors hG hM A' C D σ n b hC.le hD.le (le_max_left _ _) h hI hm p
    let inc (z : {z : ℂ // |z.re| ≤ A}) : {z : ℂ // |z.re| ≤ A'} := ⟨z.val,z.property.trans (le_max_right _ _)⟩
    exact ⟨f ∘ inc,fun z t ↦ hf (inc z) t,hb.subset (range_comp_subset_range _ _)⟩
  choose f hf hb using localFamily
  let K (z : ℂ) : SchwartzMap ℝ ℂ := f |z.re| 0 ⟨z,le_rfl⟩
  have hk (z : ℂ) (t : ℝ) : K z t = M (linePoint σ t) * spectralBoundaryKernel G (linePoint σ t) z := by
    simpa only [K,pow_zero,Complex.ofReal_one,one_mul] using hf |z.re| 0 ⟨z,le_rfl⟩ t
  refine ⟨K,hk,fun t ↦ ?_,fun A p ↦ ?_⟩
  · simp_rw [hk]
    exact (spectralBoundaryKernel_entire hG _).const_mul _
  · apply (hb A p).subset
    rintro _ ⟨z,rfl⟩
    refine ⟨z, SchwartzMap.ext fun t ↦ ?_⟩
    change f A p z t = (((1+|z.val.im|)^p:ℝ):ℂ) * K z.val t
    rw [hf,hk]

set_option backward.isDefEq.respectTransparency false

private def spectralBoundary_delta (n : ℕ) : RapidDecaySequence 1 :=
  ⟨fun a ↦ if a = latticeIndex n then 1 else 0, by
    apply (rapidSequence_mem_iff _).2
    intro k
    apply summable_of_ne_finset_zero (s := {n})
    intro m hm
    have hmn : m ≠ n := by simpa using hm
    rw [ite_eq_right (latticeIndex.injective.ne hmn),norm_zero,mul_zero]⟩

private theorem spectralBoundary_delta_eval (n m : ℕ) :
    spectralBoundary_delta n (latticeIndex m) = if m = n then 1 else 0 := by
  change (if latticeIndex m = latticeIndex n then _ else _) = _
  simp only [latticeIndex.injective.eq_iff]

private theorem spectralBoundary_delta_seminorm (n k : ℕ) :
    rapidDecaySequenceSeminorm k (spectralBoundary_delta n) = latticeWeight n ^ k := by
  rw [spectralBoundary_rapidSeminorm_eq,tsum_eq_single n]
  · simp only [spectralBoundary_delta_eval,ite_true,norm_one,mul_one]
  · intro j hj
    simp only [spectralBoundary_delta_eval,ite_eq_right hj,norm_zero,mul_zero]

private theorem spectralBoundary_delta_hasSum (s : RapidDecaySequence 1) :
    HasSum (fun n ↦ s (latticeIndex n) • spectralBoundary_delta n) s := by
  let S := RapidDecaySequence 1
  let hp := rapidDecaySequence_withSeminorms (r := 1)
  obtain ⟨_, _, _, hcomplete⟩ := (rapidDecaySequence_isFrechet (r := 1))
  let t (n : ℕ) := s (latticeIndex n) • spectralBoundary_delta n
  have hsum : Summable t := by
    apply summable_iff_cauchySeq_finset.mpr
    rw [CauchySeq, cauchy_map_iff', uniformity_eq_comap_nhds_zero, Filter.tendsto_comap_iff,
      hp.tendsto_nhds]
    intro j ε hε
    let p : Seminorm ℂ S := rapidDecaySequenceSeminorm (r := 1) j
    let L : S →ₗ[ℂ] LocalBanach p := UniformSpace.Completion.toComplL.toLinearMap.comp LinearMap.id
    have hL (x : S) : ‖L x‖ = p x := localBanach_norm_coe p x
    have h : Summable (fun n ↦ L (t n)) := by
      apply Summable.of_norm
      apply ((rapidSequence_mem_iff s.val).mp s.property j).congr
      intro n
      rw [hL]
      change _ = rapidDecaySequenceSeminorm j (s (latticeIndex n) • spectralBoundary_delta n)
      rw [map_smul_eq_mul,spectralBoundary_delta_seminorm,mul_comm]
    have hc := cauchy_map_iff'.mp (summable_iff_cauchySeq_finset.mp h)
    rw [tendsto_uniformity_iff_dist_tendsto_zero, Metric.tendsto_nhds] at hc
    filter_upwards [hc ε hε] with z hz
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_eq_norm', ← map_sum, ← map_sum,
      ← map_sub,hL] at hz
    simpa only [sub_zero,Function.comp_apply,p] using hz
  change HasSum t s
  suffices h : (∑' n,t n) = s by exact h ▸ hsum.hasSum
  apply Subtype.ext
  funext a
  obtain ⟨n,rfl⟩ := latticeIndex.surjective a
  let co : S →L[ℂ] ℂ :=
    { toFun := fun x ↦ x (latticeIndex n), map_add' _ _ := rfl, map_smul' _ _ := rfl,
      cont := rapidCoordinate_continuous n }
  change co (∑' j,t j) = s (latticeIndex n)
  rw [← (hsum.hasSum.mapL co).tsum_eq,tsum_eq_single n]
  · change s (latticeIndex n) * spectralBoundary_delta n (latticeIndex n) = _
    simp only [spectralBoundary_delta_eval,ite_true,mul_one]
  · intro m hm
    change s (latticeIndex m) * spectralBoundary_delta m (latticeIndex n) = _
    simp only [spectralBoundary_delta_eval,ite_eq_right (Ne.symm hm),mul_zero]

private theorem spectralBoundary_delta_growth {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (J : RapidDecaySequence 1 →L[ℂ] X) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n, ‖J (spectralBoundary_delta n)‖ ≤ C*latticeWeight n ^m := by
  let q := (normSeminorm ℂ X).comp J.toLinearMap
  obtain ⟨S,K,_,hK⟩ := Seminorm.bound_of_continuous rapidDecaySequence_withSeminorms q
    (show Continuous (fun x ↦ ‖J x‖) from J.continuous.norm)
  refine ⟨S.sup id,K,K.coe_nonneg,fun n ↦ (hK _).trans ?_⟩
  change (K:ℝ)*(S.sup rapidDecaySequenceSeminorm) (spectralBoundary_delta n) ≤ _
  gcongr
  apply Seminorm.finset_sup_apply_le (pow_nonneg (zero_le_one.trans (latticeWeight_bounds n).1) _)
  intro j hj
  rw [spectralBoundary_delta_seminorm]
  exact pow_le_pow_right₀ (latticeWeight_bounds n).1 (Finset.le_sup (f := id) hj)

private theorem spectralBoundary_weight_inv_sq : Summable (fun n ↦ (latticeWeight n ^ 2)⁻¹) := by
  have h := (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).comp_injective Nat.succ_injective
  apply (h.mul_left 4).of_nonneg_of_le (fun n ↦ by positivity)
  intro n
  change (latticeWeight n ^ 2)⁻¹ ≤ 4 * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
  have hn := (latticeWeight_bounds n).2.2
  have hw := (latticeWeight_bounds n).1
  rw [Nat.cast_succ, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (sq_pos_of_pos (by linarith))
    (sq_pos_of_pos (by positivity))]
  nlinarith [sq_nonneg (latticeWeight n), mul_self_le_mul_self (by positivity : 0 ≤ (n : ℝ) + 1) hn]

/-- Polynomial damping of the analysis coordinates realizes an entire Banach family
of tempered functionals in one Hilbert boundary space. -/
private theorem spectralBoundary_incoming {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (J : RapidDecaySequence 1 →L[ℂ] X) (pairing : Y →L[ℂ] X →L[ℂ] ℂ) :
    ∃ (k : ℕ) (T : Y →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2),
      ∀ y s, (∑' n : ℕ, T y n * ((latticeWeight n ^ k:ℝ):ℂ) * s (latticeIndex n)) = pairing y (J s) := by
  let H := lp (fun _ : ℕ ↦ ℂ) 2
  obtain ⟨m,C,hC,hJ⟩ := spectralBoundary_delta_growth J
  let k := m+2
  let u (n : ℕ) : H := lp.single 2 n 1
  let L (n : ℕ) := pairing.flip (J (spectralBoundary_delta n))
  let targetSet (n : ℕ) : Y →L[ℂ] H := (((latticeWeight n ^k : ℝ):ℂ)⁻¹) • (L n).smulRight (u n)
  have hw (n : ℕ) : 0 < latticeWeight n := zero_lt_one.trans_le (latticeWeight_bounds n).1
  have hu (n : ℕ) : ‖u n‖ = 1 := by simp [u,lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞))]
  have hs : Summable targetSet := by
    apply (spectralBoundary_weight_inv_sq.mul_left (‖pairing.flip‖*C)).of_norm_bounded
    intro n
    rw [show ‖targetSet n‖ = _ from norm_smul ..,ContinuousLinearMap.norm_smulRight_apply,hu,mul_one,
      norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (pow_pos (hw n) _)]
    calc
      _ ≤ (latticeWeight n^k)⁻¹ * (‖pairing.flip‖ * (C*latticeWeight n^m)) :=
        mul_le_mul_of_nonneg_left ((pairing.flip.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (hJ n) (norm_nonneg _))) (inv_nonneg.mpr (pow_nonneg (hw n).le _))
      _ = _ := by dsimp only [k]; rw [pow_add]; field_simp [(hw n).ne']
  let T := ∑' n, targetSet n
  have coord (n : ℕ) (y : Y) : T y n = ((latticeWeight n ^k:ℝ):ℂ)⁻¹ * L n y := by
    let eval := (lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 2 n).comp (ContinuousLinearMap.apply ℂ H y)
    change eval (∑' j, targetSet j) = _
    rw [← (hs.hasSum.mapL eval).tsum_eq,tsum_eq_single n]
    · change ((latticeWeight n^k:ℝ):ℂ)⁻¹ * ((L n y) * (lp.single (E := fun _ : ℕ ↦ ℂ) 2 n (1:ℂ)) n) = _
      simp
    · intro j hj
      change ((latticeWeight j^k:ℝ):ℂ)⁻¹ * ((L j y) * (lp.single (E := fun _ : ℕ ↦ ℂ) 2 j (1:ℂ)) n) = _
      simp [lp.single_apply,hj.symm]
  refine ⟨k,T,fun y s ↦ ?_⟩
  have rep := ((spectralBoundary_delta_hasSum s).mapL ((pairing y).comp J)).tsum_eq
  refine Eq.trans (tsum_congr fun n ↦ ?_) rep
  rw [coord,map_smul]
  change (((latticeWeight n^k:ℝ):ℂ)⁻¹ * L n y * ((latticeWeight n^k:ℝ):ℂ)) * s (latticeIndex n) =
    s (latticeIndex n) * L n y
  have hne : ((latticeWeight n ^ k:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (hw n).ne')
  field_simp

private theorem spectralBoundary_line_restriction (σ : ℝ) :
    ∃ L : SchwartzBergman (univ : Set ℝ) →L[ℂ] SchwartzMap ℝ ℂ,
      ∀ x t, L x t = x.val (linePoint σ t) := by
  let a : (univ : Set ℝ) := ⟨σ, mem_univ _⟩
  obtain ⟨T,hT,hE⟩ := schwartzBergman_schwartzLine_topology univ isOpen_univ ordConnected_univ univ_nonempty
  have he (x : SchwartzBergman (univ : Set ℝ)) (t : ℝ) : T x a t = x.val (linePoint σ t) := by
    simpa only [weightedVerticalTrace,pow_zero,one_mul] using hT x a t
  let L : SchwartzBergman (univ : Set ℝ) →L[ℂ] SchwartzMap ℝ ℂ := {
    toFun := fun x ↦ T x a
    map_add' := fun x y ↦ SchwartzMap.ext fun t ↦ by change T (x+y) a t = T x a t + T y a t; rw [he,he,he]; rfl
    map_smul' := fun c x ↦ SchwartzMap.ext fun t ↦ by change T (c • x) a t = c * T x a t; rw [he,he]; rfl
    cont := (continuous_apply a).comp hE.continuous }
  exact ⟨L,he⟩

/-- Restricting to a fixed vertical line gives Hilbert analysis coordinates which
reproduce integration against every Schwartz test function. -/
private theorem spectralBoundary_line_incoming (σ : ℝ) (e : SchwartzMap ℝ ℂ ≃L[ℂ] RapidDecaySequence 1) :
    ∃ (k : ℕ) (b : SchwartzBergman (univ : Set ℝ) →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2),
      ∀ x (g : SchwartzMap ℝ ℂ),
        (∑' n : ℕ, b x n * ((latticeWeight n ^ k:ℝ):ℂ) * e g (latticeIndex n)) =
          ∫ t : ℝ, x.val (linePoint σ t) * g t := by
  let μ := (volume : Measure ℝ)
  let J := (SchwartzMap.toLpCLM ℂ ℂ 2 μ).comp e.symm.toContinuousLinearMap
  let pairing := (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2
  obtain ⟨line,hline⟩ := spectralBoundary_line_restriction σ
  let b := (SchwartzMap.toLpCLM ℂ ℂ 2 μ).comp line
  obtain ⟨k,T,hT⟩ := spectralBoundary_incoming J pairing
  refine ⟨k,T.comp b,fun x g ↦ (hT (b x) (e g)).trans ?_⟩
  change (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2 ((line x).toLp 2 μ)
    ((e.symm (e g)).toLp 2 μ) = _
  rw [e.symm_apply_apply,ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(line x).coeFn_toLp 2 μ, g.coeFn_toLp 2 μ] with t ht hu
  rw [ht,hu]
  change line x t * g t = _
  rw [hline]

/-- The fixed-line Gaussian integral factors through a Hilbert space. Its output
map has rapid nuclear coefficients after composition with the quotient projection. -/
private theorem spectralBoundary_line_factorization {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    (p : ℕ → Seminorm ℂ E) (hp : WithSeminorms p) (q : SchwartzBergman (univ : Set ℝ) →L[ℂ] E)
    {G M : ℂ → ℂ} (hG : Differentiable ℂ G) (hM : Differentiable ℂ M) (σ : ℝ)
    (hd : ∀ A : ℝ, ∃ n : ℕ, ∃ C > (0:ℝ), ∀ x : ℂ, |x.re| ≤ A →
      ‖deriv G x‖ ≤ C*(1+|x.im|)^n)
    (hinv : ∃ D ≥ (1:ℝ), ∀ w : ℂ, |w.re-σ| ≤ 1 → G w ≠ 0 ∧ ‖(G w)⁻¹‖ ≤ D)
    (hm : ∀ k : ℕ, ∃ D > (0:ℝ), ∀ w : ℂ, |w.re-σ| ≤ 1 → (1+|w.im|)^k*‖M w‖ ≤ D) :
    let H := lp (fun _ : ℕ ↦ ℂ) 2
    let sourceSpace := SchwartzBergman (univ : Set ℝ)
    ∃ (b : sourceSpace →L[ℂ] H) (R : H →L[ℂ] sourceSpace),
      (∀ x z, (R (b x)).val z = ∫ t : ℝ,
        (M (linePoint σ t) * x.val (linePoint σ t)) * spectralBoundaryKernel G (linePoint σ t) z) ∧
      ∃ r : NuclearPresentation (q.comp R), ∀ j : ℕ, ∃ D : ℝ, ∀ n : ℕ, ‖r.coeff n‖*((n:ℝ)+1)^j ≤ D := by
  obtain ⟨D,hD,hI⟩ := hinv
  obtain ⟨K,he,hk,hb⟩ := spectralBoundary_global_kernel hG hM σ hd
    ⟨0,D,zero_lt_one.trans_le hD, by simpa only [pow_zero,mul_one] using hI⟩ hm
  obtain ⟨e⟩ := realSchwartz_equiv_rapidDecay
  obtain ⟨k,b,hin⟩ := spectralBoundary_line_incoming σ e
  obtain ⟨R,hout,r,hr⟩ := spectralBoundary_contour_presentation p hp K hk hb e k q
  refine ⟨b,R,fun x z ↦ ?_, r, hr⟩
  rw [hout,hin]
  apply integral_congr_ae
  exact ae_of_all _ fun t ↦ by
    change x.val (linePoint σ t) * K z t = _
    rw [he]; ring

private theorem spectralBoundary_order_of_bound {ρ : ℂ} {F : ℂ → ℂ} (hf : AnalyticAt ℂ F ρ)
    (m : ℕ) (h : F =O[𝓝 ρ] (fun z ↦ (z-ρ)^m)) :
    m ≤ analyticOrderAt F ρ := by
  by_contra! hl
  have hn : analyticOrderAt F ρ ≠ ⊤ := hl.ne_top
  have hlt : analyticOrderNatAt F ρ < m := by
    exact_mod_cast (show (analyticOrderNatAt F ρ : ℕ∞) < (m:ℕ∞) by
      rwa [show (analyticOrderNatAt F ρ : ℕ∞) = analyticOrderAt F ρ from ENat.natCast_toNat hn])
  have hsmall : (fun z : ℂ ↦ (z-ρ)^m) =o[𝓝 ρ] (fun z ↦ (z-ρ)^analyticOrderNatAt F ρ) :=
    (isLittleO_pow_pow (𝕜 := ℂ) hlt).comp_tendsto (by simpa using (continuousAt_id (x := ρ)).sub_const ρ)
  have hnon : ∀ᶠ z : ℂ in 𝓝[≠] ρ, (z-ρ)^analyticOrderNatAt F ρ ≠ 0 :=
    by filter_upwards [self_mem_nhdsWithin] with z hz using pow_ne_zero _ (sub_ne_zero.mpr hz)
  exact isLittleO_irrefl hnon.frequently
    (((hf.isTheta_pow_sub hn).2.trans h).trans_isLittleO hsmall |>.mono nhdsWithin_le_nhds)

private theorem spectralBoundary_bound_of_order {ρ : ℂ} {G : ℂ → ℂ} (hg : AnalyticAt ℂ G ρ)
    (m : ℕ) (hm : m ≤ analyticOrderAt G ρ) :
    G =O[𝓝 ρ] (fun z ↦ (z-ρ)^m) := by
  obtain ⟨g,hg',he⟩ := (natCast_le_analyticOrderAt hg).mp hm
  apply (show G =ᶠ[𝓝 ρ] (fun z ↦ (z-ρ)^m • g z) from he).isBigO.trans
  simpa only [smul_eq_mul,mul_one] using
    (isBigO_refl (fun z : ℂ ↦ (z-ρ)^m) (𝓝 ρ)).mul (hg'.continuousAt.isBigO_one ℂ)

/-- On a neighborhood disjoint from a boundary line, the difference between the
regularized and bare Gaussian integrals is bounded by a constant times the generator. -/
private theorem spectralBoundary_line_error {G : ℂ → ℂ} (hG : Continuous G) (σ : ℝ)
    (C : ℝ) (_hC : 0 ≤ C) (hc : ∀ t : ℝ, G (linePoint σ t) ≠ 0 ∧ ‖(G (linePoint σ t))⁻¹‖ ≤ C)
    (f : ℝ → ℂ) (hf : Continuous f) (hi : Integrable f) (ρ : ℂ) (hρ : ρ.re ≠ σ) :
    (fun z : ℂ ↦ (∫ t : ℝ, f t * spectralBoundaryKernel G (linePoint σ t) z)
        - (∫ t : ℝ, Complex.exp ((z-linePoint σ t)^2) * f t / (linePoint σ t-z))) =O[𝓝 ρ] G := by
  let δ := |ρ.re-σ|/2
  let T := |ρ.re-σ|+1
  let sourceSpace := Real.exp (T^2)/δ
  have hd : 0 < δ := half_pos (abs_pos.mpr (sub_ne_zero.mpr hρ))
  have hT : 0 < T := by dsimp [T]; positivity
  have hB : 0 ≤ sourceSpace := div_nonneg (Real.exp_pos _).le hd.le
  have hnear : ∀ᶠ z : ℂ in 𝓝 ρ, |z.re-σ| ∈ Ioo δ T := by
    apply (show ContinuousAt (fun z : ℂ ↦ |z.re-σ|) ρ by fun_prop).eventually_mem
    exact Ioo_mem_nhds (half_lt_self (abs_pos.mpr (sub_ne_zero.mpr hρ))) (by dsimp [T]; linarith)
  apply IsBigO.of_bound ((sourceSpace*C) * ∫ t : ℝ, ‖f t‖)
  filter_upwards [hnear] with z hz
  let w (t : ℝ) := linePoint σ t
  let a (t : ℝ) := Complex.exp ((z-w t)^2) * f t / (w t-z)
  let b (t : ℝ) := a t / G (w t) * G z
  have hwre (t : ℝ) : (w t).re = σ := by simp [w]
  have hw (t : ℝ) : δ ≤ ‖w t-z‖ := by
    calc δ ≤ |z.re - σ| := hz.1.le
         _ = |(w t-z).re| := by rw [Complex.sub_re,hwre,abs_sub_comm]
         _ ≤ _ := Complex.abs_re_le_norm _
  have hw' (t : ℝ) : w t - z ≠ 0 := norm_pos_iff.mp (hd.trans_le (hw t))
  have ha (t : ℝ) : ‖a t‖ ≤ sourceSpace * ‖f t‖ := by
    have he : ‖Complex.exp ((z-w t)^2)‖ ≤ Real.exp (T^2) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [pow_two,Complex.mul_re,Complex.sub_re,Complex.sub_im,hwre]
      nlinarith [sq_abs (z.re-σ), mul_self_le_mul_self (abs_nonneg _) hz.2.le,sq_nonneg (z.im-(w t).im)]
    change ‖Complex.exp ((z-w t)^2)*f t/(w t-z)‖ ≤ _
    rw [norm_div,norm_mul,div_le_iff₀ (hd.trans_le (hw t))]
    calc
      _ ≤ Real.exp (T^2)*‖f t‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ = (sourceSpace*‖f t‖)*δ := by dsimp [sourceSpace]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hw t) (mul_nonneg hB (norm_nonneg _))
  have hb (t : ℝ) : ‖b t‖ ≤ ((sourceSpace*C)*‖G z‖)*‖f t‖ := by
    change ‖a t / G (w t) * G z‖ ≤ _
    rw [div_eq_mul_inv,norm_mul,norm_mul]
    calc
      _ ≤ (sourceSpace*‖f t‖*C)*‖G z‖ := by gcongr; exacts [ha t,(hc t).2]
      _ = _ := by ring
  have hcw : Continuous w := by fun_prop
  have hca : Continuous a := by dsimp [a]; fun_prop (disch := exact hw' _)
  have hcb : Continuous b := (hca.div (hG.comp hcw) (fun t ↦ (hc t).1)).mul continuous_const
  have hai := (hi.norm.const_mul sourceSpace).mono' hca.aestronglyMeasurable (ae_of_all _ ha)
  have hbi := (hi.norm.const_mul ((sourceSpace*C)*‖G z‖)).mono' hcb.aestronglyMeasurable (ae_of_all _ hb)
  have heq (t : ℝ) : f t * spectralBoundaryKernel G (w t) z = a t - b t := by
    rw [spectralBoundaryKernel_offPole (Ne.symm (sub_ne_zero.mp (hw' t))) (hc t).1]
    dsimp only [a,b]
    ring
  change ‖(∫ t : ℝ, f t * spectralBoundaryKernel G (w t) z) - ∫ t : ℝ, a t‖ ≤ _
  simp_rw [heq]
  rw [integral_sub hai hbi,sub_sub_cancel_left,norm_neg]
  calc
    _ ≤ ∫ t : ℝ, ((sourceSpace*C)*‖G z‖)*‖f t‖ :=
      norm_integral_le_of_norm_le (hi.norm.const_mul _) (ae_of_all _ hb)
    _ = _ := by rw [integral_const_mul]; ring

private theorem spectralGaussian_strip {z : ℂ} {a b : ℝ} (f : SchwartzBergman (univ : Set ℝ)) (hab : a<b) :
    UniformlySchwartzOnStrip (fun w ↦ Complex.exp ((z-w)^2) * f.val w) a b := by
  have hf : Differentiable ℂ f.val := fun w ↦
    (f.property.2.1 w (mem_univ _)).differentiableAt (univ_mem' fun _ ↦ mem_univ _)
  have hdiff : Differentiable ℂ (fun w ↦ Complex.exp ((z-w)^2) * f.val w) := by fun_prop
  refine ⟨hab,hdiff.differentiableOn,?_⟩
  intro δ hδ hwidth N _
  obtain ⟨C,hC⟩ := f.property.2.2 a b hab.le (subset_univ _) N
  let T := |z.re|+|a|+|b|
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨Real.exp (T^2) * (|C|+1), by positivity, ?_⟩
  have ht : ∀ᶠ y : ℝ in comap abs atTop, 0 < |y| := tendsto_comap.eventually (eventually_gt_atTop 0)
  filter_upwards [ht] with y hy
  intro σ hσ
  let w := (σ:ℂ) + (y:ℂ)*Complex.I
  have re : w.re = σ := by simp [w]
  have im : w.im = y := by simp [w]
  have hσ' : σ ∈ Icc a b := ⟨by linarith [hσ.1],by linarith [hσ.2]⟩
  have haσ : |σ| ≤ |a|+|b| := abs_le.mpr
    ⟨by linarith [hσ'.1,neg_abs_le a,abs_nonneg b],by linarith [hσ'.2,le_abs_self b,abs_nonneg a]⟩
  have hr : |z.re-w.re| ≤ T := (abs_sub _ _).trans (by dsimp [T];rw [re];linarith)
  have hg : ‖Complex.exp ((z-w)^2)‖ ≤ Real.exp (T^2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [pow_two,Complex.mul_re,Complex.sub_re,Complex.sub_im]
    nlinarith [sq_abs (z.re-w.re),mul_nonneg (sub_nonneg.mpr hr) (add_nonneg hT (abs_nonneg (z.re-w.re))),sq_nonneg (z.im-w.im)]
  have hfc : ‖w‖^N * ‖f.val w‖ ≤ C := by
    simpa only [norm_mul,norm_pow] using hC ⟨w,show w.re ∈ Icc a b from re ▸ hσ',rfl⟩
  have hi : |y| ≤ ‖w‖ := im ▸ Complex.abs_im_le_norm w
  change ‖Complex.exp ((z-w)^2) * f.val w‖ ≤ _
  rw [norm_mul,le_div_iff₀ (pow_pos hy _)]
  calc
    _ = ‖Complex.exp ((z-w)^2)‖ * (|y|^N * ‖f.val w‖) := by ring
    _ ≤ Real.exp (T^2) * (‖w‖^N * ‖f.val w‖) := by gcongr
    _ ≤ Real.exp (T^2) * (|C|+1) := by gcongr; linarith [le_abs_self C]

/-- On two fixed lines a Gaussian-localized Cauchy integral recovers the original
Schwartz–Bergman function at every point strictly between the lines. -/
private theorem spectralBoundary_cauchy (f : SchwartzBergman (univ : Set ℝ))
    (c d : ℝ) (z : ℂ) (hz : z.re ∈ Ioo c d) :
    let Φ := fun w ↦ Complex.exp ((z-w)^2) * f.val w
    (∫ t : ℝ, Φ ((d:ℂ)+t*Complex.I) / ((d:ℂ)+t*Complex.I-z)) -
    (∫ t : ℝ, Φ ((c:ℂ)+t*Complex.I) / ((c:ℂ)+t*Complex.I-z)) =
      2*(Real.pi:ℂ)*f.val z := by
  dsimp only
  let Φ := fun w ↦ Complex.exp ((z-w)^2) * f.val w
  have hΦ : UniformlySchwartzOnStrip Φ (c-1) (d+1) := spectralGaussian_strip f (by linarith [hz.1,hz.2])
  have hc : c-1+1 = c := by ring
  have hd : d+1-1 = d := by ring
  have h := asymptoticCauchy_eq_iteratedDeriv hΦ 1 one_pos (by rw [hc,hd];exact hz.1.trans hz.2) 0 z (by rwa [hc,hd])
  simp only [hc,hd,Nat.factorial_zero,Nat.cast_one,zero_add,pow_one,iteratedDeriv_zero,verticalLineIntegral] at h
  have hΦz : Φ z = f.val z := by simp [Φ]
  rw [hΦz] at h
  change (∫ t : ℝ, Φ ((d:ℂ)+t*Complex.I) / ((d:ℂ)+t*Complex.I-z)) -
    (∫ t : ℝ, Φ ((c:ℂ)+t*Complex.I) / ((c:ℂ)+t*Complex.I-z)) = _
  field_simp [Real.pi_ne_zero, Complex.I_ne_zero] at h
  simpa only [mul_comm Complex.I] using h

/-- The signed pair of regularized Gaussian lines has the same finite jet as the
original test at each common zero of the indicated order. -/
private theorem spectralBoundary_signed_jets (c d : ℝ) (G₀ G₁ : ℂ → ℂ) (F region targetSet : SchwartzBergman (univ : Set ℝ))
    (ρ : ℂ) (hρ : ρ.re ∈ Ioo c d) (m : ℕ)
    (hG₀ : Differentiable ℂ G₀) (hG₁ : Differentiable ℂ G₁)
    (hv₀ : ∃ D ≥ (1:ℝ), ∀ t, G₀ (linePoint d t) ≠ 0 ∧ ‖(G₀ (linePoint d t))⁻¹‖ ≤ D)
    (hv₁ : ∃ D ≥ (1:ℝ), ∀ t, G₁ (linePoint c t) ≠ 0 ∧ ‖(G₁ (linePoint c t))⁻¹‖ ≤ D)
    (ho₀ : m ≤ analyticOrderAt G₀ ρ) (ho₁ : m ≤ analyticOrderAt G₁ ρ)
    (hU : ∀ z, region.val z = ∫ t : ℝ, F.val (linePoint d t) * spectralBoundaryKernel G₀ (linePoint d t) z)
    (hV : ∀ z, targetSet.val z = ∫ t : ℝ, F.val (linePoint c t) * spectralBoundaryKernel G₁ (linePoint c t) z)
    (j : ℕ) (hj : j < m) :
    iteratedDeriv j ((2*(Real.pi:ℂ))⁻¹ • region + (-(2*(Real.pi:ℂ))⁻¹) • targetSet - F).val ρ = 0 := by
  let bare (s : ℝ) (z : ℂ) := ∫ t : ℝ, Complex.exp ((z-linePoint s t)^2) * F.val (linePoint s t)/(linePoint s t-z)
  let p := fun z : ℂ ↦ (z-ρ)^m
  have err (G : ℂ → ℂ) (s : ℝ) (region' : SchwartzBergman (univ : Set ℝ)) (hs : ρ.re ≠ s)
      (hg : Differentiable ℂ G) (ho : m ≤ analyticOrderAt G ρ)
      (hv : ∃ D ≥ (1:ℝ), ∀ t, G (linePoint s t) ≠ 0 ∧ ‖(G (linePoint s t))⁻¹‖ ≤ D)
      (hu : ∀ z, region'.val z = ∫ t : ℝ, F.val (linePoint s t) * spectralBoundaryKernel G (linePoint s t) z) :
      (fun z ↦ region'.val z - bare s z) =O[𝓝 ρ] p := by
    obtain ⟨D,hD,hv⟩ := hv
    obtain ⟨line,hl⟩ := spectralBoundary_line_restriction s
    have hb := spectralBoundary_line_error hg.continuous s D (zero_le_one.trans hD) hv
      (line F) (line F).continuous (line F).integrable ρ hs
    have he : (fun z ↦ region'.val z - bare s z) = (fun z : ℂ ↦ (∫ t : ℝ, line F t * spectralBoundaryKernel G (linePoint s t) z)
        - (∫ t : ℝ, Complex.exp ((z-linePoint s t)^2) * line F t / (linePoint s t-z))) := by
      funext z
      simp only [hu,hl,bare]
    rw [he]
    exact hb.trans (spectralBoundary_bound_of_order (hg.analyticAt ρ) m ho)
  have h₀ := err G₀ d region hρ.2.ne hG₀ ho₀ hv₀ hU
  have h₁ := err G₁ c targetSet hρ.1.ne' hG₁ ho₁ hv₁ hV
  let α : ℂ := (2*(Real.pi:ℂ))⁻¹
  let S := α • region + (-α) • targetSet - F
  have he : S.val =ᶠ[𝓝 ρ] fun z ↦ α * ((region.val z-bare d z) - (targetSet.val z-bare c z)) := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually_mem (Ioo_mem_nhds hρ.1 hρ.2)] with z hz
    have hc : bare d z - bare c z = 2*(Real.pi:ℂ)*F.val z := spectralBoundary_cauchy F c d z hz
    change α * region.val z + (-α) * targetSet.val z - F.val z = _
    have ha : α * (2*(Real.pi:ℂ)) = 1 := inv_mul_cancel₀ (by exact_mod_cast mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero)
    linear_combination α * hc + F.val z * ha
  have han : AnalyticAt ℂ S.val ρ :=
    ((show Differentiable ℂ S.val from fun z ↦
      (S.property.2.1 z (mem_univ _)).differentiableAt (univ_mem' fun _ ↦ mem_univ _))).analyticAt ρ
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han).mp
    (spectralBoundary_order_of_bound han m (he.isBigO.trans ((h₀.sub h₁).const_mul_left α))) j hj

private theorem spectralBoundary_countable_seminorms (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [PolynormableSpace ℂ E] [FirstCountableTopology E] :
    ∃ p : ℕ → Seminorm ℂ E, WithSeminorms p := by
  classical
  obtain ⟨region,hU⟩ := (𝓝 (0:E)).exists_antitone_basis
  choose p hp hsub using fun n ↦ (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp (hU.mem n)
  refine ⟨p,SeminormFamily.withSeminorms_of_hasBasis p ((hU.1).to_hasBasis ?_ ?_)⟩
  · intro n _
    exact ⟨(p n).ball 0 1,SeminormFamily.basisSets_singleton_mem p n one_pos,hsub n⟩
  · intro targetSet hV
    obtain ⟨s,r,hr,rfl⟩ := (SeminormFamily.basisSets_iff p).mp hV
    exact hU.1.mem_iff.mp ((s.sup p).ball_mem_nhds (Seminorm.continuous_finsetSup (fun i _ ↦ hp i)) hr)
private theorem spectralBoundary_interleaved_decay (c₀ c₁ : ℕ → ℂ)
    (hr₀ : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖c₀ n‖ * ((n:ℝ)+1)^k ≤ C)
    (hr₁ : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖c₁ n‖ * ((n:ℝ)+1)^k ≤ C)
    (k : ℕ) : ∃ C : ℝ, ∀ n : ℕ,
      ‖Sum.elim c₀ c₁ (Equiv.natSumNatEquivNat.symm n)‖ * ((n:ℝ)+1)^k ≤ C := by
  let e := Equiv.natSumNatEquivNat
  let c := Sum.elim c₀ c₁
  obtain ⟨A,hA⟩ := hr₀ k
  obtain ⟨sourceSpace,hB⟩ := hr₁ k
  refine ⟨2^k*max A sourceSpace,fun n ↦ ?_⟩
  obtain ⟨i,rfl⟩ := e.surjective n
  change ‖c (e.symm (e i))‖ * ((e i:ℕ)+1:ℝ)^k ≤ _
  rw [e.symm_apply_apply]
  have heval : ∀ j : ℕ, (e (Sum.inl j) : ℕ) = 2*j ∧ e (Sum.inr j) = 2*j+1 :=
    fun j ↦ ⟨congrFun Equiv.natSumNatEquivNat_apply (Sum.inl j),congrFun Equiv.natSumNatEquivNat_apply (Sum.inr j)⟩
  cases i with
  | inl j =>
    rw [(heval j).1]
    change ‖c₀ j‖ * _ ≤ _
    push_cast
    have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2*j+1) (by linarith : (2:ℝ)*j+1 ≤ 2*(j+1)) k
    rw [mul_pow] at hpow
    calc
      _ ≤ ‖c₀ j‖*(2^k*((j:ℝ)+1)^k) := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = 2^k*(‖c₀ j‖*((j:ℝ)+1)^k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((hA j).trans (le_max_left ..)) (by positivity)
  | inr j =>
    rw [(heval j).2]
    change ‖c₁ j‖ * _ ≤ _
    push_cast
    rw [show (2:ℝ)*j+1+1=2*((j:ℝ)+1) by ring,mul_pow,mul_left_comm]
    exact mul_le_mul_of_nonneg_left ((hB j).trans (le_max_right ..)) (by positivity)

private theorem spectralBoundary_interleaved_equicontinuous {X H₀ H₁ : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup H₀] [NormedSpace ℂ H₀] [NormedAddCommGroup H₁] [NormedSpace ℂ H₁]
    (l₀ : ℕ → H₀ →L[ℂ] ℂ) (l₁ : ℕ → H₁ →L[ℂ] ℂ)
    (h₀ : EquicontinuousAt (fun n t ↦ l₀ n t) 0)
    (h₁ : EquicontinuousAt (fun n t ↦ l₁ n t) 0)
    (P₀ : X →L[ℂ] H₀) (P₁ : X →L[ℂ] H₁) :
    let d := Sum.elim (fun n ↦ (l₀ n).comp P₀) (fun n ↦ (l₁ n).comp P₁)
    EquicontinuousAt (fun n t ↦ d (Equiv.natSumNatEquivNat.symm n) t) 0 := by
  intro d targetSet hV
  have hu := (P₀.continuous.tendsto' 0 0 (map_zero P₀)).eventually (h₀ targetSet hV)
  have hv := (P₁.continuous.tendsto' 0 0 (map_zero P₁)).eventually (h₁ targetSet hV)
  filter_upwards [hu,hv] with x hx hy n
  cases e : Equiv.natSumNatEquivNat.symm n with
  | inl j => simpa only [d,Sum.elim_inl,ContinuousLinearMap.comp_apply,map_zero] using hx j
  | inr j => simpa only [d,Sum.elim_inr,ContinuousLinearMap.comp_apply,map_zero] using hy j

set_option backward.isDefEq.respectTransparency false in
/-- Finite interleaving of two rapid presentations over a common source, after
precomposition with arbitrary bounded maps. A jointly bounded family of target vectors
gives one Banach disc, even when the original presentations used different discs. -/
private theorem spectralBoundary_interleave {X H₀ H₁ E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup H₀] [NormedSpace ℂ H₀]
    [NormedAddCommGroup H₁] [NormedSpace ℂ H₁]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    {S₀ : H₀ →L[ℂ] E} {S₁ : H₁ →L[ℂ] E}
    (r₀ : NuclearPresentation S₀) (r₁ : NuclearPresentation S₁)
    (hr₀ : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖r₀.coeff n‖ * ((n:ℝ)+1)^k ≤ C)
    (hr₁ : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖r₁.coeff n‖ * ((n:ℝ)+1)^k ≤ C)
    (P₀ : X →L[ℂ] H₀) (P₁ : X →L[ℂ] H₁) :
    ∃ r : NuclearPresentation (S₀.comp P₀ + S₁.comp P₁),
      ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖r.coeff n‖ * ((n:ℝ)+1)^k ≤ C := by
  classical
  let e := Equiv.natSumNatEquivNat
  let c : ℕ⊕ℕ → ℂ := Sum.elim r₀.coeff r₁.coeff
  let d : ℕ⊕ℕ → X →L[ℂ] ℂ := Sum.elim (fun n ↦ (r₀.functional n).comp P₀) (fun n ↦ (r₁.functional n).comp P₁)
  let v : ℕ⊕ℕ → E := Sum.elim (fun n ↦ (r₀.vector n:E)) (fun n ↦ (r₁.vector n:E))
  have hb : IsVonNBounded ℂ (range v) := by
    apply (r₀.isBanachDisc.bounded.union r₁.isBanachDisc.bounded).subset
    rintro _ ⟨i,rfl⟩
    cases i with
    | inl n => exact Or.inl (r₀.vector_mem n)
    | inr n => exact Or.inr (r₁.vector_mem n)
  obtain ⟨D,hD,hmem⟩ := exists_isBanachDisc_of_isVonNBounded_range v hb
  let w (n : ℕ) : Submodule.span ℂ D := ⟨v (e.symm n),Submodule.subset_span (hmem (e.symm n))⟩
  let r : NuclearPresentation (S₀.comp P₀ + S₁.comp P₁) := {
    coeff := c ∘ e.symm
    functional := d ∘ e.symm
    vector := w
    disc := D
    isBanachDisc := hD
    vector_mem := fun n ↦ hmem (e.symm n)
    summable_coeff := by
      have h : Summable (fun i ↦ ‖c i‖) := Summable.sum _ r₀.summable_coeff r₁.summable_coeff
      exact (e.symm.summable_iff (f := fun i ↦ ‖c i‖)).mpr h
    equicontinuous := spectralBoundary_interleaved_equicontinuous r₀.functional r₁.functional r₀.equicontinuous r₁.equicontinuous P₀ P₁
    hasSum := by
      intro x
      let f (i : ℕ⊕ℕ) := (c i * d i x) • v i
      have h : HasSum f (S₀ (P₀ x) + S₁ (P₁ x)) := HasSum.sum (f := f) (r₀.hasSum (P₀ x)) (r₁.hasSum (P₁ x))
      exact (e.symm.hasSum_iff (f := f) (a := S₀ (P₀ x) + S₁ (P₁ x))).mpr h }
  refine ⟨r,?_⟩
  change ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖c (e.symm n)‖ * ((n:ℝ)+1)^k ≤ C
  exact spectralBoundary_interleaved_decay r₀.coeff r₁.coeff hr₀ hr₁

/-- The two boundary actions descend jointly through the spectral quotient. Coefficients
may encode either orientation or the Cauchy normalization. The Hilbert product permits
orthogonal elimination of the full synthesis kernel after taking their signed sum. -/
private theorem spectralBoundary_two_sided_descent {sourceSpace H₀ H₁ E : Type*}
    [AddCommGroup sourceSpace] [Module ℂ sourceSpace] [TopologicalSpace sourceSpace]
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    (q : sourceSpace →L[ℂ] E) (hq : Topology.IsQuotientMap q) (T : E →L[ℂ] E)
    (b₀ : sourceSpace →L[ℂ] H₀) (b₁ : sourceSpace →L[ℂ] H₁)
    (S₀ : H₀ →L[ℂ] E) (S₁ : H₁ →L[ℂ] E) (c₀ c₁ : ℂ)
    (r₀ : NuclearPresentation S₀) (r₁ : NuclearPresentation S₁)
    (hr₀ : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖r₀.coeff n‖ * ((n:ℝ)+1)^k ≤ C)
    (hr₁ : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖r₁.coeff n‖ * ((n:ℝ)+1)^k ≤ C)
    (hT : ∀ x, c₀ • S₀ (b₀ x) + c₁ • S₁ (b₁ x) = T (q x)) :
    IsStronglyNuclearOperator T := by
  let H := WithLp 2 (H₀ × H₁)
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ H₀ H₁
  let P₀ : H →L[ℂ] H₀ := (ContinuousLinearMap.fst ℂ H₀ H₁).comp e.toContinuousLinearMap
  let P₁ : H →L[ℂ] H₁ := (ContinuousLinearMap.snd ℂ H₀ H₁).comp e.toContinuousLinearMap
  let S : H →L[ℂ] E := S₀.comp P₀ + S₁.comp P₁
  let b : sourceSpace →L[ℂ] H := e.symm.toContinuousLinearMap.comp ((c₀ • b₀).prod (c₁ • b₁))
  obtain ⟨r,hr⟩ := spectralBoundary_interleave r₀ r₁ hr₀ hr₁ P₀ P₁
  apply spectralBoundary_strong_of_synthesis q hq b S T _ r hr
  intro x
  change S₀ (e (e.symm ((c₀ • b₀) x,(c₁ • b₁) x))).1 + S₁ (e (e.symm ((c₀ • b₀) x,(c₁ • b₁) x))).2 = _
  simpa using hT x

private theorem spectralBoundary_globalStrip {f : ℂ → ℂ} (hc : Continuous f) {a b : ℝ}
    (decay : ∀ k : ℕ, 1 ≤ k → ∃ C > (0:ℝ), ∀ᶠ y : ℝ in comap abs atTop, ∀ t ∈ Icc a b,
      ‖f ((t : ℂ) + y * Complex.I)‖ ≤ C / |y|^k) (k : ℕ) :
    ∃ C > (0:ℝ), ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ * (1 + |z.im|)^k ≤ C := by
  obtain ⟨C,hC,h⟩ := decay (k+1) (by omega)
  obtain ⟨R,hR⟩ := eventually_atTop.1 (eventually_comap.mp h)
  let M := |a| + |b| + |R| + 2
  let w (z : ℂ) : ℝ := ‖f z‖ * (1 + |z.im|)^k
  have hw : Continuous w := hc.norm.mul ((continuous_const.add Complex.continuous_im.abs).pow k)
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0 : ℂ) M).bddAbove_image hw.continuousOn
  refine ⟨max D (C*2^k),lt_of_lt_of_le (by positivity : 0 < C*2^k) (le_max_right _ _),?_⟩
  intro z hz
  by_cases hy : max R 1 ≤ |z.im|
  · have hy1 : 1 ≤ |z.im| := (le_max_right _ _).trans hy
    have h0 : 0 < |z.im| := zero_lt_one.trans_le hy1
    have hg := hR |z.im| ((le_max_left _ _).trans hy) z.im rfl z.re hz
    rw [Complex.re_add_im] at hg
    have hh := (le_div_iff₀ (pow_pos h0 _)).mp hg
    have hpow : (1 + |z.im|)^k ≤ 2^k * |z.im|^k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) k
    have hpow' : |z.im|^k ≤ |z.im|^(k+1) := by
      rw [pow_succ]; exact le_mul_of_one_le_right (by positivity) hy1
    apply le_trans _ (le_max_right _ _)
    calc
      _ ≤ ‖f z‖ * (2^k * |z.im|^k) := by gcongr
      _ ≤ ‖f z‖ * (2^k * |z.im|^(k+1)) := by gcongr
      _ = (‖f z‖ * |z.im|^(k+1)) * 2^k := by ring
      _ ≤ _ := by gcongr
  · apply le_trans _ (le_max_left _ _)
    apply hD ⟨z,?_,rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |z.re| ≤ |a| + |b| := abs_le.mpr ⟨by linarith [hz.1, neg_abs_le a, abs_nonneg b],
      by linarith [hz.2,le_abs_self b,abs_nonneg a]⟩
    have hi : |z.im| < max R 1 := lt_of_not_ge hy
    have hh : max R 1 ≤ |R|+1 := max_le (by linarith [le_abs_self R]) (by linarith [abs_nonneg R])
    dsimp [M]
    linarith [Complex.norm_le_abs_re_add_abs_im z]

end SpectralBoundarySynthesis

section SpectralBoundaryArithmetic

open Filter Metric Asymptotics

private theorem spectralBoundary_strip_estimate {L : ℂ → ℂ} (σ : ℝ) (hL : MeromorphicNFOn L univ)
    (hGrowth : ∀ a b : ℝ, a < b → ∃ M : ℝ, 0 < M ∧ (L : ℂ → ℂ) =O[comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun z : ℂ ↦ |Complex.im z| ^ M) (R : ℝ) (hR : 0 < R) :
    ∃ C M T : ℝ, 0 < C ∧ 0 < M ∧ ∀ z : ℂ, |z.re - σ| ≤ R → T < |z.im| →
      AnalyticAt ℂ L z ∧ ‖L z‖ ≤ C * |z.im| ^ M := by
  let a := σ - R - 1
  let b := σ + R + 1
  obtain ⟨M, hM, hg⟩ := hGrowth a b (by dsimp [a, b]; linarith)
  obtain ⟨C, hC, hg⟩ := Asymptotics.isBigO_iff'.mp hg
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hg
  obtain ⟨T, hT⟩ := hg
  have hB (z : ℂ) (hz : z.re ∈ Icc a b) (ht : T ≤ |z.im|) :
      ‖L z‖ ≤ C * |z.im| ^ M := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hT _ ht z rfl hz
  refine ⟨C, M, T, hC, hM, fun z hz ht ↦ ⟨?_, hB _ ⟨?_, ?_⟩ ht.le⟩⟩ <;>
    try first | (dsimp [a, b]; linarith [(abs_le.mp hz).1, (abs_le.mp hz).2])
  apply (hL (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra! hp
  have hr : z.re ∈ Ioo a b := by
    constructor <;> dsimp [a, b] <;> linarith [(abs_le.mp hz).1, (abs_le.mp hz).2]
  have him : Continuous (fun u : ℂ ↦ |u.im|) := Complex.continuous_im.abs
  have hn₁ := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hr
  have hn₂ : ∀ᶠ u : ℂ in 𝓝 z, |u.im| ∈ Ioo T (|z.im| + 1) :=
    (isOpen_Ioo.preimage him).mem_nhds ⟨ht, by linarith⟩
  have hbnd : ∀ᶠ u : ℂ in 𝓝 z, ‖L u‖ ≤ C * (|z.im| + 1) ^ M := by
    filter_upwards [hn₁, hn₂] with u hu hv
    exact (hB u ⟨hu.1.le, hu.2.le⟩ hv.1.le).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hv.2.le hM.le) hC.le)
  have hinf := (tendsto_norm_cobounded_atTop.comp
    (tendsto_cobounded_of_meromorphicOrderAt_neg hp)).eventually_gt_atTop (C * (|z.im| + 1) ^ M)
  obtain ⟨u, hu, hv⟩ := ((hbnd.filter_mono nhdsWithin_le_nhds).and hinf).exists
  exact (not_lt_of_ge hu) hv

local notation "Λr" => Λ(χ, τ, hτ)

/-- The gamma-stripped, pole-cleared entire spectral generator of the early spectral section. -/
private def spectralFiniteG (z : ℂ) := (heckeGammaFactor χ z)⁻¹ * (Λr).val z

private theorem spectralFiniteG_diff : Differentiable ℂ (spectralFiniteG χ τ hτ) :=
  (differentiable_inv_heckeGammaFactor χ).mul (Λr).property

private def spectralFiniteP (z : ℂ) : ℂ := open Classical in
  let b := ((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℂ)*Complex.I
  let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
  (z+b)^δ * (1-z-b)^δ

private theorem spectralFiniteP_diff : Differentiable ℂ (spectralFiniteP χ τ hτ) := by
  unfold spectralFiniteP; fun_prop

private theorem spectralFiniteP_ne {z : ℂ} (hz : 1 < z.re) : spectralFiniteP χ τ hτ z ≠ 0 := by
  dsimp only [spectralFiniteP]
  apply mul_ne_zero <;> apply pow_ne_zero <;> intro he <;> have h := congrArg Complex.re he <;> simp [Complex.mul_re] at h <;> linarith

private theorem spectralFiniteG_right {z : ℂ} (hz : 1 < z.re) :
    spectralFiniteG χ τ hτ z = spectralFiniteP χ τ hτ z * finiteHeckeL χ ⟨z,hz⟩ := by
  let polarPoly := spectralFiniteP χ τ hτ
  let L := continuedCompletedHeckeL χ
  obtain ⟨hL,hse⟩ := continuedCompletedHeckeL_spec χ
  have hP := spectralFiniteP_diff χ τ hτ
  have hm : MeromorphicOn (polarPoly*L) univ := fun s _ ↦ (hP.analyticAt s).meromorphicAt.mul (hL (mem_univ s)).meromorphicAt
  have hNF := (meromorphicNFAt_mul_iff_right (hP.analyticAt z) (spectralFiniteP_ne χ τ hτ hz)).2 (hL (mem_univ z))
  change (heckeGammaFactor χ z)⁻¹ * toMeromorphicNFOn (polarPoly*L) univ z = _
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ z),toMeromorphicNFAt_eq_self.mpr hNF]
  change (heckeGammaFactor χ z)⁻¹ * (polarPoly z*L z) = polarPoly z*_
  have hγ := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)
  rw [show L z = heckeGammaFactor χ z * finiteHeckeL χ ⟨z,hz⟩ from hse ⟨z,hz⟩]
  field_simp

private theorem spectralFiniteG_eq_finite (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hseries : ∀ s : {s : ℂ // 1<s.re}, L s = finiteHeckeL χ s) :
    spectralFiniteG χ τ hτ = toMeromorphicNFOn (spectralFiniteP χ τ hτ * L) univ := by
  have hn : MeromorphicNFOn (spectralFiniteG χ τ hτ) univ := fun s _ ↦ ((spectralFiniteG_diff χ τ hτ).analyticAt s).meromorphicNFAt
  have hm : MeromorphicOn (spectralFiniteP χ τ hτ * L) univ := fun s _ ↦
    ((spectralFiniteP_diff χ τ hτ).analyticAt s).meromorphicAt.mul (hL (mem_univ s)).meromorphicAt
  rw [←toMeromorphicNFOn_eq_self.mpr hn]
  apply heckeEulerProductOutside_eq_finite_nf_eq _ _ hn.meromorphicOn hm
  intro x hx
  rw [spectralFiniteG_right χ τ hτ hx]
  change _ = _ * L x
  rw [hseries ⟨x,hx⟩]

private theorem spectralFiniteG_order (z : ℂ) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) z ≤ meromorphicOrderAt (spectralFiniteG χ τ hτ) z := by
  obtain ⟨L,hL,hseries,hord⟩ := spectralNuclearity_trace_finite_companion χ
  have hP := (spectralFiniteP_diff χ τ hτ).analyticAt
  have hm : MeromorphicOn (spectralFiniteP χ τ hτ * L) univ := fun s _ ↦
    (hP s).meromorphicAt.mul (hL (mem_univ s)).meromorphicAt
  rw [spectralFiniteG_eq_finite χ τ hτ L hL hseries,meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ _),
    meromorphicOrderAt_mul (hP z).meromorphicAt (hL (mem_univ z)).meromorphicAt]
  exact (hord z).trans (le_add_of_nonneg_left (hP z).meromorphicOrderAt_nonneg)

/-- Each retained multiplicity is dominated by the analytic order of the entire
finite generator at the shifted site used by the actual spectral quotient. -/
private theorem spectralBoundaryFinite_shifted_retained_order (a : ℝ) (z : ℂ)
    (hz : 0 < analyticOrderAt ((Λr).val : ℂ → ℂ) z) :
    ((analyticOrderAt ((Λr).val : ℂ → ℂ) z).toNat : ℕ∞) ≤
      analyticOrderAt (fun s ↦ (spectralFiniteG χ τ hτ) (s + (a:ℂ))) (z - (a:ℂ)) := by
  obtain ⟨k, hk, hreg, hord⟩ := spectralNuclearity_trace_zero_order χ τ hτ ⟨z,hz⟩
  change analyticOrderAt ((Λr).val : ℂ → ℂ) z = (k:ℕ∞) at hreg
  have hZ := (continuedCompletedHeckeL_spec χ).1
  rw [MeromorphicOn.divisor_apply hZ.meromorphicOn (mem_univ _)] at hord
  have hzord : meromorphicOrderAt (continuedCompletedHeckeL χ) z = (k:ℤ) := by
    cases h : meromorphicOrderAt (continuedCompletedHeckeL χ) z with
    | top => rw [h] at hord; simp at hord; omega
    | coe i => rw [h] at hord; simpa using congrArg (fun n : ℤ ↦ (n:WithTop ℤ)) hord
  have hfin := spectralFiniteG_order χ τ hτ z
  rw [hzord,((spectralFiniteG_diff χ τ hτ).analyticAt z).meromorphicOrderAt_eq] at hfin
  have hshift : analyticOrderAt (fun s ↦ (spectralFiniteG χ τ hτ) (s+(a:ℂ))) (z-(a:ℂ)) =
      analyticOrderAt ((spectralFiniteG χ τ hτ):ℂ → ℂ) z := by
    rw [show (fun s ↦ (spectralFiniteG χ τ hτ) (s+(a:ℂ))) =
      ((spectralFiniteG χ τ hτ) : ℂ → ℂ) ∘ (fun s : ℂ ↦ s+(a:ℂ)) by rfl,
      analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp),sub_add_cancel]
  rw [hshift,hreg,ENat.toNat_natCast]
  cases hh : analyticOrderAt ((spectralFiniteG χ τ hτ):ℂ → ℂ) z with
  | top => exact le_top
  | coe n => rw [hh,ENat.map_natCast] at hfin; exact_mod_cast hfin

/-- The entire pole-cleared finite generator has a polynomial bound uniformly up
and down each fixed strip, including its continued values in the finite-height region. -/
private theorem spectralBoundaryFinite_strip_growth (W : ℝ) :
    ∃ n : ℕ, ∃ C > (0:ℝ), ∀ z : ℂ, |z.re| ≤ W →
      ‖(spectralFiniteG χ τ hτ) z‖ ≤ C*(1+|z.im|)^n := by
  classical
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL,hs⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  let t := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let p := spectralFiniteP χ τ hτ
  let G := spectralFiniteG χ τ hτ
  have hp := spectralFiniteP_diff χ τ hτ
  have hm : MeromorphicOn (p*L) univ := fun z _ ↦ (hp.analyticAt z).meromorphicAt.mul (hL (mem_univ z)).meromorphicAt
  have he (z : ℂ) (hz : AnalyticAt ℂ L z) : G z = p z * L z := by
    change spectralFiniteG χ τ hτ z = _
    rw [spectralFiniteG_eq_finite χ τ hτ L hL hs,toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr ((hp.analyticAt z).mul hz).meromorphicNFAt]
    rfl
  let polarPoly := |W|+|t|+3
  have hP : 1 ≤ polarPoly := by dsimp [polarPoly]; linarith [abs_nonneg W,abs_nonneg t]
  have hpb (z : ℂ) (hz : |z.re|≤W) : ‖p z‖ ≤ polarPoly^2*(1+|z.im|)^2 := by
    let b := (t:ℂ)*Complex.I
    have hbn : ‖b‖=|t| := by simp [b]
    have hu : polarPoly + |z.im| ≤ polarPoly*(1+|z.im|) := by nlinarith [mul_le_mul_of_nonneg_right hP (abs_nonneg z.im)]
    have hz1 := Complex.norm_le_abs_re_add_abs_im z
    have h1 : ‖z+b‖ ≤ polarPoly*(1+|z.im|) := (norm_add_le _ _).trans (by rw [hbn]; apply le_trans _ hu; dsimp [polarPoly]; linarith [le_abs_self W])
    have h2 : ‖1-z-b‖ ≤ polarPoly*(1+|z.im|) := calc
      _ ≤ ‖1-z‖+‖b‖ := norm_sub_le _ _
      _ ≤ (‖(1:ℂ)‖+‖z‖)+|t| := by rw [hbn]; exact add_le_add_left (norm_sub_le _ _) _
      _ ≤ _ := by rw [norm_one]; apply le_trans _ hu; dsimp [polarPoly]; linarith [le_abs_self W]
    by_cases hd : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype=1
    · change ‖(z+b)^(if _ then (1:ℕ) else 0)*(1-z-b)^(if _ then (1:ℕ) else 0)‖ ≤ _
      simp only [hd,ite_true,pow_one,norm_mul]
      rw [←mul_pow,pow_two]
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    · change ‖(z+b)^(if _ then (1:ℕ) else 0)*(1-z-b)^(if _ then (1:ℕ) else 0)‖ ≤ _
      simp only [ite_eq_right hd,pow_zero,mul_one,norm_one]
      apply one_le_mul_of_one_le_of_one_le <;> apply one_le_pow₀
      · exact hP
      · linarith [abs_nonneg z.im]
  obtain ⟨D,M,T,hD,hM,hgrowth⟩ := spectralBoundary_strip_estimate 0 hL
    (finiteHeckeL_continuation_isBigO_rpow χ L hL hs) (|W|+1) (by positivity)
  have hG : Continuous G := (spectralFiniteG_diff χ τ hτ).continuous
  obtain ⟨A,hA⟩ := (isCompact_closedBall (0:ℂ) (|W|+|T|+1)).exists_bound_of_continuousOn hG.continuousOn
  let n := ⌈M⌉₊
  let C := max 1 (max A (polarPoly^2*D))
  have hC : 1 ≤ C := le_max_left _ _
  refine ⟨n+2,C,zero_lt_one.trans_le hC,?_⟩
  intro z hz
  let H := 1+|z.im|
  have hH : 1 ≤ H := by dsimp [H]; linarith [abs_nonneg z.im]
  by_cases ht : T < |z.im|
  · obtain ⟨ha,hgrow⟩ := hgrowth z (by rw [sub_zero]; linarith [le_abs_self W]) ht
    have hpow : |z.im|^M ≤ H^n := calc
      _ ≤ H^M := Real.rpow_le_rpow (abs_nonneg _) (by dsimp [H]; linarith) hM.le
      _ ≤ H^(n:ℝ) := Real.rpow_le_rpow_of_exponent_le hH (Nat.le_ceil M)
      _ = _ := Real.rpow_natCast ..
    change ‖G z‖ ≤ C*H^(n+2)
    rw [he z ha,norm_mul]
    calc
      _ ≤ (polarPoly^2*H^2)*(D*H^n) := mul_le_mul (hpb z hz) (hgrow.trans (mul_le_mul_of_nonneg_left hpow hD.le)) (norm_nonneg _) (by positivity)
      _ = (polarPoly^2*D)*H^(n+2) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)
  · have hmem : z ∈ closedBall (0:ℂ) (|W|+|T|+1) := by
      rw [mem_closedBall,dist_zero_right]
      linarith [Complex.norm_le_abs_re_add_abs_im z,le_abs_self W,le_abs_self T]
    have hb : ‖G z‖ ≤ C := (hA z hmem).trans ((le_max_left _ _).trans (le_max_right _ _))
    exact hb.trans (le_mul_of_one_le_right (zero_le_one.trans hC) (one_le_pow₀ hH))

/-- In every fixed vertical strip and after any real shift, the derivative of the
actual finite generator has at most polynomial growth in absolute height. -/
private theorem spectralBoundaryFinite_shifted_deriv (a W : ℝ) :
    ∃ n : ℕ, ∃ C > (0:ℝ), ∀ z : ℂ, |z.re| ≤ W →
      ‖deriv (fun s ↦ (spectralFiniteG χ τ hτ) (s+(a:ℂ))) z‖ ≤
        C*(1+|z.im|)^n := by
  let G : ℂ → ℂ := (spectralFiniteG χ τ hτ)
  have hd : Differentiable ℂ G := (spectralFiniteG_diff χ τ hτ)
  let g (s : ℂ) := G (s+(a:ℂ))
  have hgd : Differentiable ℂ g := hd.comp (differentiable_id.add_const _)
  obtain ⟨n,C,hC,hb⟩ := spectralBoundaryFinite_strip_growth χ τ hτ (W+|a|+1)
  refine ⟨n,C*2^n,by positivity,?_⟩
  intro z hz
  have hloc (u : ℂ) (hu : u ∈ sphere z 1) : ‖g u‖ ≤ (C*2^n)*(1+|z.im|)^n := by
    have hdist : ‖u-z‖ = 1 := mem_sphere_iff_norm.mp hu
    have hr : |(u+(a:ℂ)).re| ≤ W+|a|+1 := by
      simp only [Complex.add_re,Complex.ofReal_re]
      have hr := (Complex.abs_re_le_norm (u-z)).trans hdist.le
      change |u.re-z.re| ≤ 1 at hr
      have hx := (abs_le.mp ((abs_abs_sub_abs_le_abs_sub u.re z.re).trans hr)).2
      linarith [abs_add_le u.re a]
    have hi : 1+|(u+(a:ℂ)).im| ≤ 2*(1+|z.im|) := by
      simp only [Complex.add_im,Complex.ofReal_im,add_zero]
      have hr := (Complex.abs_im_le_norm (u-z)).trans hdist.le
      change |u.im-z.im| ≤ 1 at hr
      have hx := (abs_le.mp ((abs_abs_sub_abs_le_abs_sub u.im z.im).trans hr)).2
      linarith [abs_nonneg z.im]
    refine (hb _ hr).trans ?_
    rw [mul_assoc,mul_comm (2^n),←mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by simpa [mul_comm] using hi) _) hC.le
  simpa using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hgd.diffContOnCl hloc

/-- Functional reflection transfers each retained jet to the entire finite generator
of the contragredient. The multiplication here is by a nowhere-zero entire epsilon factor. -/
private theorem spectralBoundaryFinite_reflected_retained_order (a : ℝ) (z : ℂ)
    (hz : 0 < analyticOrderAt ((Λr).val : ℂ → ℂ) z) :
    ((analyticOrderAt ((Λr).val : ℂ → ℂ) z).toNat : ℕ∞) ≤
      analyticOrderAt (fun s ↦ (spectralFiniteG χ⁻¹ τ hτ) (1-(s+(a:ℂ)))) (z - (a:ℂ)) := by
  let L := continuedCompletedHeckeL χ
  let Ld := continuedCompletedHeckeL χ⁻¹
  obtain ⟨hL,heL⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨hLd,heLd⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε,hε,hnε,hfe⟩ := completedHeckeL_continuation_functionalEquation χ _ _ hL heL hLd heLd
  have hcomp : meromorphicOrderAt (fun s ↦ Ld (1-s)) z = meromorphicOrderAt Ld (1-z) := by
    simpa [Function.comp_def] using meromorphicOrderAt_comp_of_deriv_ne_zero (f := Ld)
      (show AnalyticAt ℂ (fun s : ℂ ↦ 1-s) z by fun_prop)
      (show deriv (fun s : ℂ ↦ 1-s) z ≠ 0 by simp)
  rw [show (fun s ↦ Ld (1-s)) = ε*L from funext hfe,meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt _) (hnε _)] at hcomp
  obtain ⟨k, hk, hreg, hord⟩ := spectralNuclearity_trace_zero_order χ τ hτ ⟨z,hz⟩
  change analyticOrderAt ((Λr).val : ℂ → ℂ) z = (k:ℕ∞) at hreg
  rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)] at hord
  have hzord : meromorphicOrderAt L z = (k:ℤ) := by
    change (meromorphicOrderAt L z).untop₀ = (k:ℤ) at hord
    cases h : meromorphicOrderAt L z with
    | top => rw [h] at hord; simp at hord; omega
    | coe i => rw [h] at hord; simpa using congrArg (fun n : ℤ ↦ (n:WithTop ℤ)) hord
  have hfin := spectralFiniteG_order χ⁻¹ τ hτ (1-z)
  change meromorphicOrderAt Ld (1-z) ≤ _ at hfin
  rw [←hcomp,hzord,((spectralFiniteG_diff χ⁻¹ τ hτ).analyticAt _).meromorphicOrderAt_eq] at hfin
  have hshift : analyticOrderAt (fun s ↦ (spectralFiniteG χ⁻¹ τ hτ) (1-(s+(a:ℂ)))) (z-(a:ℂ)) =
      analyticOrderAt ((spectralFiniteG χ⁻¹ τ hτ):ℂ→ℂ) (1-z) := by
    rw [show (fun s ↦ (spectralFiniteG χ⁻¹ τ hτ) (1-(s+(a:ℂ)))) =
      ((spectralFiniteG χ⁻¹ τ hτ) : ℂ → ℂ) ∘ (fun s : ℂ ↦ 1-(s+(a:ℂ))) by rfl,
      analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp),sub_add_cancel]
  rw [hshift,hreg,ENat.toNat_natCast]
  cases hh : analyticOrderAt ((spectralFiniteG χ⁻¹ τ hτ):ℂ → ℂ) (1-z) with
  | top => exact le_top
  | coe n => rw [hh,ENat.map_natCast] at hfin; exact_mod_cast hfin

private theorem spectralBoundaryFinite_reflected_deriv (a W : ℝ) :
    ∃ n : ℕ, ∃ C > (0:ℝ), ∀ z : ℂ, |z.re| ≤ W →
      ‖deriv (fun s ↦ (spectralFiniteG χ⁻¹ τ hτ) (1-(s+(a:ℂ)))) z‖ ≤ C*(1+|z.im|)^n := by
  let g (s : ℂ) := (spectralFiniteG χ⁻¹ τ hτ) (s+((1-a:ℝ):ℂ))
  have hg : Differentiable ℂ g := (spectralFiniteG_diff χ⁻¹ τ hτ).comp (differentiable_id.add_const _)
  obtain ⟨n,C,hC,hb⟩ := spectralBoundaryFinite_shifted_deriv χ⁻¹ τ hτ (1-a) W
  refine ⟨n,C,hC,fun z hz ↦ ?_⟩
  have hn : ∀ s : ℂ, 1-(s+(a:ℂ)) = -s+((1-a:ℝ):ℂ) := by intro s; push_cast; ring
  simp only [hn]
  change ‖deriv (g ∘ fun s : ℂ ↦ -s) z‖ ≤ _
  have hdn : HasDerivAt (fun s : ℂ ↦ -s) (-1) z := (hasDerivAt_id z).neg
  have hdcomp := ((hg (-z)).hasDerivAt).comp z hdn
  rw [hdcomp.deriv]
  have he := hb (-z) (by simpa using hz)
  simpa [g] using he
local notation "domainSet" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "fp(" χ ")" => (ideleClassNormTwist χ 0)

/-- Absolute convergence at two gives a single upper bound on the entire closed
right half-plane. -/
private theorem spectralBoundaryFinite_euler_lower
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ, 2 ≤ z.re →
      (ideleClassNormTwist χ 0).LSeries z ≠ 0 ∧ ‖((ideleClassNormTwist χ 0).LSeries z)⁻¹‖ ≤ C := by
  let r (v : HeightOneSpectrum (𝓞 F)) : ℝ := (v.asIdeal.absNorm : ℝ)^(-(2:ℝ))
  have hr : Summable r := (summable_absNorm_rpow F (by norm_num : (1:ℝ)<2)).comp_injective
    (fun _ _ he ↦ HeightOneSpectrum.ext he)
  have hr₀ (v) : 0 ≤ r v := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let C := Real.exp (∑' v,r v)
  have hC : 1 ≤ C := Real.one_le_exp (tsum_nonneg hr₀)
  refine ⟨C,hC,fun z hz ↦ ?_⟩
  have hf (v : HeightOneSpectrum (𝓞 F)) : 1 ≤ Real.exp (r v) * ‖finiteHeckeEulerFactor χ v z‖ := by
    rw [finiteHeckeEulerFactor]
    split_ifs with hu
    · let q := (v.asIdeal.absNorm : ℝ)
      let b := (ideleClassNormTwist χ 0).localValue v * (q : ℂ)^(-z)
      have hq : 1 < q := by dsimp only [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
      have hw : ‖b‖ ≤ r v := by
        rw [show ‖b‖ = _ from norm_mul ..,norm_ideleClassNormTwist_zero_localValue χ v,
          one_mul,Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq),Complex.neg_re]
        exact Real.rpow_le_rpow_of_exponent_le hq.le (neg_le_neg hz)
      have hlt : r v < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num)
      have hne : 1-b ≠ 0 := sub_ne_zero.mpr (fun e ↦ by rw [←e,norm_one] at hw; linarith)
      change 1 ≤ Real.exp (r v) * ‖(1-b)⁻¹‖
      rw [norm_inv,←div_eq_mul_inv,one_le_div (norm_pos_iff.mpr hne)]
      exact (norm_sub_le _ _).trans ((by rw [norm_one]; linarith : ‖(1:ℂ)‖+‖b‖ ≤ 1+r v).trans
        (by simpa only [add_comm] using Real.add_one_le_exp (r v)))
    · simpa only [norm_one,mul_one] using Real.one_le_exp (hr₀ v)
  have raw : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) ↦ ∏ v ∈ S, finiteHeckeEulerFactor χ v z)
      atTop (𝓝 ((ideleClassNormTwist χ 0).LSeries z)) := finiteHeckeL_hasProd χ ⟨z,show 1 < z.re by linarith⟩
  have hs : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) ↦ ∏ v ∈ S, ‖finiteHeckeEulerFactor χ v z‖)
      atTop (𝓝 ‖(ideleClassNormTwist χ 0).LSeries z‖) := by simpa only [norm_prod] using raw.norm
  have hbound : 1 ≤ C * ‖(ideleClassNormTwist χ 0).LSeries z‖ := by
    apply ge_of_tendsto' (hs.const_mul C)
    intro S
    have hprod := Finset.one_le_prod₀ (s := S) (fun v _ ↦ hf v)
    rw [Finset.prod_mul_distrib,← Real.exp_sum] at hprod
    change 1 ≤ C * ∏ v ∈ S, ‖finiteHeckeEulerFactor χ v z‖
    exact hprod.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (hr.sum_le_tsum S (fun v _ ↦ hr₀ v)))
      (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _))
  have hne : (ideleClassNormTwist χ 0).LSeries z ≠ 0 := by intro e; norm_num [e] at hbound
  exact ⟨hne,by rw [norm_inv,inv_le_iff_one_le_mul₀ (norm_pos_iff.mpr hne)]; simpa only [mul_comm] using hbound⟩

/-- On the absolute-convergence half-plane the pole-clearing polynomial has modulus at least
one. The actual entire finite generator therefore has a uniformly bounded reciprocal there. -/
private theorem spectralBoundaryFinite_right_reciprocal (χ : domainSet) (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F)
    (hτ : RightInverse τ (ideleNorm F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ, 2 ≤ z.re →
      (spectralFiniteG χ τ hτ) z ≠ 0 ∧
        ‖((spectralFiniteG χ τ hτ) z)⁻¹‖ ≤ C := by
  classical
  obtain ⟨C,hC,he⟩ := spectralBoundaryFinite_euler_lower χ
  refine ⟨C,hC,fun z hz ↦ ?_⟩
  let t := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let b := (t:ℂ)*Complex.I
  let p := spectralFiniteP χ τ hτ z
  have h1 : 1≤‖z+b‖ := calc
    _ ≤ z.re := by linarith
    _ = (z+b).re := by simp [b,Complex.mul_re]
    _ ≤ _ := Complex.re_le_norm _
  have h2 : 1≤‖1-z-b‖ := calc
    _ ≤ -(1-z-b).re := by simp [b,Complex.mul_re]; linarith
    _ ≤ |(1-z-b).re| := neg_le_abs _
    _ ≤ _ := Complex.abs_re_le_norm _
  have hp : 1≤‖p‖ := by
    change 1≤‖(z+b)^(if _ then (1:ℕ) else 0)*(1-z-b)^(if _ then (1:ℕ) else 0)‖
    rw [norm_mul,norm_pow,norm_pow]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1) (one_le_pow₀ h2)
  have hval := spectralFiniteG_right χ τ hτ (show 1<z.re by linarith)
  change spectralFiniteG χ τ hτ z = p*(fp(χ)).LSeries z at hval
  rw [hval]
  obtain ⟨hn,hinv⟩ := he z hz
  refine ⟨mul_ne_zero (norm_pos_iff.mp (zero_lt_one.trans_le hp)) hn,?_⟩
  rw [mul_inv, norm_mul]
  exact (mul_le_of_le_one_left (by positivity) (by simpa using inv_le_one_of_one_le₀ hp)).trans hinv
/-- Both boundary kernels for the genuine quotient admit entire numerators, uniform
reciprocal bounds in unit neighborhoods of their respective integration lines, full
retained orders and polynomial derivative growth on every finite vertical strip. -/
private theorem spectralBoundaryFinite_boundary_arithmetic (a : ℝ) :
    let conditions (G : ℂ → ℂ) (σ : ℝ) :=
      Differentiable ℂ G ∧
      (∀ z : ℂ, 0 < analyticOrderAt ((Λr).val:ℂ → ℂ) z →
        ((analyticOrderAt ((Λr).val:ℂ → ℂ) z).toNat:ℕ∞) ≤ analyticOrderAt G (z-(a:ℂ))) ∧
      (∀ W : ℝ, ∃ n : ℕ, ∃ C > (0:ℝ), ∀ z : ℂ, |z.re| ≤ W → ‖deriv G z‖ ≤ C*(1+|z.im|)^n) ∧
      (∃ C ≥ (1:ℝ), ∀ z : ℂ, |z.re-σ| ≤ 1 → G z ≠ 0 ∧ ‖(G z)⁻¹‖ ≤ C)
    conditions (fun s ↦ (spectralFiniteG χ τ hτ) (s+(a:ℂ))) (3-a) ∧
    conditions (fun s ↦ (spectralFiniteG χ⁻¹ τ hτ) (1-(s+(a:ℂ)))) (-2-a) := by
  intro conditions
  constructor
  · refine ⟨(spectralFiniteG_diff χ τ hτ).comp (differentiable_id.add_const _),
      spectralBoundaryFinite_shifted_retained_order χ τ hτ a,spectralBoundaryFinite_shifted_deriv χ τ hτ a,?_⟩
    obtain ⟨C,hC,hb⟩ := spectralBoundaryFinite_right_reciprocal χ τ hτ
    refine ⟨C,hC,fun z hz ↦ hb _ ?_⟩
    simp only [Complex.add_re,Complex.ofReal_re]
    linarith [(abs_le.mp hz).1]
  · refine ⟨(spectralFiniteG_diff χ⁻¹ τ hτ).comp (show Differentiable ℂ (fun s : ℂ ↦ 1-(s+(a:ℂ))) by fun_prop),
      spectralBoundaryFinite_reflected_retained_order χ τ hτ a,spectralBoundaryFinite_reflected_deriv χ τ hτ a,?_⟩
    obtain ⟨C,hC,hb⟩ := spectralBoundaryFinite_right_reciprocal χ⁻¹ τ hτ
    refine ⟨C,hC,fun z hz ↦ hb _ ?_⟩
    simp only [Complex.sub_re,Complex.one_re,Complex.add_re,Complex.ofReal_re]
    linarith [(abs_le.mp hz).2]

end SpectralBoundaryArithmetic

open Classical in
/-- Paper: Theorem 7.4.1.1(2), p. 367. The remaining operator input is the
existence of a rapidly decreasing nuclear presentation of the retained-jet action. -/
private theorem spectralNuclearity_strong_of_jet_action (a : ℝ) (N : ℕ) (hN : 0 < N) (φ : 𝒟)
    (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a)))
    (hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) :
    let K := ⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker
    let E := Q(a) ⧸ K
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    ∀ (A : B →L[ℂ] B) (Aq : Q(a) →L[ℂ] Q(a)) (T : E →L[ℂ] E),
      (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) →
      (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) →
      (∀ x, T (K.mkQ x) = K.mkQ (Aq x)) →
      IsStronglyNuclearOperator T := by
  classical
  intro K E A Aq T hA hAq hT
  clear hN
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let D := D(a)
  let I := {i : jets(χ, τ, hτ) // i.2.val < N}
  have hD : IsClosed (D : Set B) := schwartzBergmanDivisible_isClosed _
  have hK : IsClosed (K : Set (Q(a))) := by
    change IsClosed (↑(⨅ i : I, (d i.val).toLinearMap.ker) : Set (Q(a)))
    rw [Submodule.coe_iInf]
    exact isClosed_iInter (fun i ↦ (d i.val).isClosed_ker)
  have hB := schwartzBergman_frechet univ isOpen_univ ordConnected_univ univ_nonempty
  have hQ := isFrechetTVS_quotient hB D hD
  obtain ⟨_, hp, hmet, hcomplete⟩ := isFrechetTVS_quotient hQ K hK
  let : PolynormableSpace ℂ E := hp
  let : TopologicalSpace.MetrizableSpace E := hmet
  let : CompleteSpace E := hcomplete
  let q : B →L[ℂ] E := K.mkQL.comp D.mkQL
  have hq : Topology.IsQuotientMap q := (Submodule.isQuotientMap_mkQ K).comp (Submodule.isQuotientMap_mkQ D)
  obtain ⟨p,hp'⟩ := spectralBoundary_countable_seminorms E
  let M := nuclearityTestMellin χ φ
  have hM : Differentiable ℂ M := archNuclearityDenominator_closed_invariant_multiplier χ φ
  have decay (σ : ℝ) (k : ℕ) : ∃ C > (0:ℝ), ∀ w : ℂ, |w.re-σ| ≤ 1 → (1+|w.im|)^k*‖M w‖ ≤ C := by
    obtain ⟨C,hC,h⟩ := spectralBoundary_globalStrip hM.continuous
      (spectralNuclearity_trace_vertical_decay χ φ (σ-1) (σ+1) (by linarith)) k
    exact ⟨C,hC,fun w hw ↦ by rw [mul_comm]; exact h w ⟨by linarith [(abs_le.mp hw).1], by linarith [(abs_le.mp hw).2]⟩⟩
  let G₀ := fun s : ℂ ↦ (spectralFiniteG χ τ hτ) (s+(a:ℂ))
  let G₁ := fun s : ℂ ↦ (spectralFiniteG χ⁻¹ τ hτ) (1-(s+(a:ℂ)))
  obtain ⟨⟨hg₀,ho₀,hd₀,hi₀⟩,hg₁,ho₁,hd₁,hi₁⟩ := spectralBoundaryFinite_boundary_arithmetic χ τ hτ a
  obtain ⟨b₀,R₀,h₀,r₀,hr₀⟩ := spectralBoundary_line_factorization p hp' q (G := G₀) hg₀ hM (3-a) hd₀ hi₀ (decay _)
  obtain ⟨b₁,R₁,h₁,r₁,hr₁⟩ := spectralBoundary_line_factorization p hp' q (G := G₁) hg₁ hM (-2-a) hd₁ hi₁ (decay _)
  let α : ℂ := (2*(Real.pi:ℂ))⁻¹
  apply spectralBoundary_two_sided_descent q hq T b₀ b₁ (q.comp R₀) (q.comp R₁) α (-α) r₀ r₁ hr₀ hr₁
  intro x
  change α • q (R₀ (b₀ x)) + (-α) • q (R₁ (b₁ x)) = T (K.mkQ (D.mkQ x))
  rw [hT,hAq]
  change α • q (R₀ (b₀ x)) + (-α) • q (R₁ (b₁ x)) = q (A x)
  let X := α • R₀ (b₀ x) + (-α) • R₁ (b₁ x) - A x
  suffices hx : q X = 0 by simpa only [X,map_sub,map_add,map_smul,sub_eq_zero] using hx
  change K.mkQ (D.mkQ X) = 0
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,Submodule.mem_iInf]
  intro i
  change d i.val (D.mkQ X) = 0
  rw [hd]
  let z := i.val.1
  obtain ⟨k,hk,_,hdiv⟩ := spectralNuclearity_trace_zero_order χ τ hτ z
  have strip := spectralNuclearity_trace_zero_strip χ (z := z.val) (by rw [hdiv]; exact_mod_cast hk)
  have hs : (z.val-(a:ℂ)).re ∈ Ioo (-2-a) (3-a) := by
    simp only [Complex.sub_re,Complex.ofReal_re,mem_Ioo]
    exact ⟨by linarith [strip.1],by linarith [strip.2]⟩
  have hi (G : ℂ → ℂ) (s : ℝ) (h : ∃ C ≥ (1:ℝ), ∀ w : ℂ, |w.re-s| ≤ 1 → G w ≠ 0 ∧ ‖(G w)⁻¹‖ ≤ C) :
      ∃ C ≥ (1:ℝ), ∀ t : ℝ, G ((s:ℂ)+t*Complex.I) ≠ 0 ∧ ‖(G ((s:ℂ)+t*Complex.I))⁻¹‖ ≤ C := by
    obtain ⟨C,hC,h⟩ := h
    exact ⟨C,hC,fun t ↦ h _ (by simp)⟩
  apply spectralBoundary_signed_jets (-2-a) (3-a) G₀ G₁ (A x) (R₀ (b₀ x)) (R₁ (b₁ x))
    (z.val-(a:ℂ)) hs (multiplicity(χ,τ,hτ,z)) hg₀ hg₁ (hi _ _ hi₀) (hi _ _ hi₁)
    (ho₀ z.val z.property) (ho₁ z.val z.property) _ _ i.val.2.val i.val.2.isLt
  · intro w
    simpa only [hA,M] using h₀ x w
  · intro w
    simpa only [hA,M] using h₁ x w

open Classical in
/-- Paper: Theorem 7.4.1.1(2), pp. 366–367. One rapidly decreasing presentation
of the descended operator whose scalar series sums to the explicit zero formula. -/
private theorem spectralNuclearity_trace_presentation (a : ℝ) (N : ℕ) (hN : 0 < N) (φ : 𝒟)
    (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a)))
    (hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) :
    let K := ⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker
    let E := Q(a) ⧸ K
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    let term := fun z : zeros(χ, τ, hτ) ↦
      ((min N (multiplicity(χ, τ, hτ, z)) : ℕ) : ℂ) * nuclearityTestMellin χ φ (z.val - (a : ℂ))
    ∀ (A : B →L[ℂ] B) (Aq : Q(a) →L[ℂ] Q(a)) (T : E →L[ℂ] E),
      (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) →
      (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) →
      (∀ x, T (K.mkQ x) = K.mkQ (Aq x)) →
      ∃ r : NuclearPresentation T, (∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
        ‖r.coeff n‖ * ((n : ℝ) + 1)^k ≤ C) ∧
        HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) (∑' z, term z) := by
  intro K E term A Aq T hA hAq hT
  obtain ⟨r, hr⟩ := spectralNuclearity_strong_of_jet_action χ τ hτ a N hN φ d hd A Aq T hA hAq hT
  exact ⟨r, hr, spectralNuclearity_trace_of_rapid_presentation χ τ hτ a N φ d hd A Aq T hA hAq hT r hr⟩

open Classical in
/-- Paper: Theorem 7.4.1.1(2), pp. 366–367. The Mellin action on the quotient
by the first `N` jets is strongly nuclear, and every nuclear presentation has the
trace determined by its jet blocks. -/
theorem spectralNuclearity_trace_of_jet_action (a : ℝ) (N : ℕ) (hN : 0 < N) (φ : 𝒟)
    (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a)))
    (hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) :
    let K := ⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker
    let E := Q(a) ⧸ K
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    let term := fun z : zeros(χ, τ, hτ) ↦
      ((min N (multiplicity(χ, τ, hτ, z)) : ℕ) : ℂ) * nuclearityTestMellin χ φ (z.val - (a : ℂ))
    ∀ (A : B →L[ℂ] B) (Aq : Q(a) →L[ℂ] Q(a)) (T : E →L[ℂ] E),
      (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) →
      (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) →
      (∀ x, T (K.mkQ x) = K.mkQ (Aq x)) →
      IsStronglyNuclearOperator T ∧ ∀ r : NuclearPresentation T,
        HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) (∑' z, term z) := by
  intro K E term A Aq T hA hAq hT
  obtain ⟨r, hfast, htrace⟩ :=
    spectralNuclearity_trace_presentation χ τ hτ a N hN φ d hd A Aq T hA hAq hT
  refine ⟨⟨r, hfast⟩, ?_⟩
  obtain ⟨v, hv, _⟩ := spectralJet_unique_presentation_sum χ τ hτ a N d T ⟨r⟩
  have he := (hv r).2.unique htrace
  intro t
  exact he ▸ (hv t).2

open Classical in
/-- Paper: Theorem 7.4.1.1(2), pp. 366–367.
Compactly supported tests act on the quotient determined by the first N derivatives
in each block. Every nuclear presentation of the order-zero action has the stated trace.
Deviation: The printed span of the first N primal vectors can fail to be invariant.
Quotient by the common kernel of the retained derivative functionals. The multiplier
is evaluated at z − a for each unshifted zero z. -/
theorem spectralNuclearity_trace (a : ℝ) (N : ℕ) (_hN : 0 < N) (φ : 𝒟)
    (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a)))
    (_hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) :
    let K := ⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker
    let E := Q(a) ⧸ K
    letI instSpectralUniformSec4 : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    let term := fun z : zeros(χ, τ, hτ) ↦
      ((min N (multiplicity(χ, τ, hτ, z)) : ℕ) : ℂ) * nuclearityTestMellin χ φ (z.val - (a : ℂ))
    ∃ (A : B →L[ℂ] B) (T : E →L[ℂ] E),
      (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) ∧
      (∃ Aq : Q(a) →L[ℂ] Q(a),
        (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) ∧
        ∀ x : Q(a), T (K.mkQ x) = K.mkQ (Aq x)) ∧
      IsStronglyNuclearOperator T ∧ Summable (fun z ↦ ‖term z‖) ∧
      ∀ r : NuclearPresentation T,
        HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) (∑' z, term z) := by
  intro K E term
  obtain ⟨A, hA, hD⟩ := (spectralNuclearityDenominator_closed_invariant χ τ hτ a φ).2
  obtain ⟨Aq, T, hAq, hT⟩ := spectralNuclearity_trace_descends χ τ hτ a N φ d _hd A hA hD
  obtain ⟨hnuclear, htrace⟩ :=
    spectralNuclearity_trace_of_jet_action χ τ hτ a N _hN φ d _hd A Aq T hA hAq hT
  exact ⟨A, T, hA, ⟨Aq, hAq, hT⟩, hnuclear,
    spectralNuclearity_trace_term_summable χ τ hτ a N φ, htrace⟩

end Spectral

section Orbital

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

/-- A quotient map followed by a closed embedding gives the same closed embedding on the kernel quotient. -/
private theorem exists_polarThetaNuclearityAction_closedEmbedding_of_factor
    {X Y Target : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Target] [Module ℂ Target] [TopologicalSpace Target]
    (N : Submodule ℂ X) (q : X →L[ℂ] Y) (hq : IsQuotientMap q)
    (hqker : q.ker = N) (j : Y →L[ℂ] Target) (hj : IsClosedEmbedding j)
    (Z : (X ⧸ N) →L[ℂ] Target) (hZ : ∀ x, Z (N.mkQ x) = j (q x)) :
    IsClosedEmbedding Z := by
  obtain ⟨e, he⟩ := exists_quotient_equiv_of_kernel q hq N hqker
  have heq : (Z : (X ⧸ N) → Target) = j ∘ e := by
    funext x
    obtain ⟨u, rfl⟩ := N.mkQ_surjective x
    exact (hZ u).trans (congrArg j (he u).symm)
  rw [heq]
  exact hj.comp e.toHomeomorph.isClosedEmbedding

/-- An open map onto a closed linear range identifies its kernel quotient with that range. -/
private theorem exists_polarThetaNuclearityAction_closedEmbedding_of_range
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (N : Submodule ℂ X) (T : X →L[ℂ] Y)
    (ho : IsOpenMap T.rangeRestrict) (hc : IsClosed (Set.range T))
    (hk : T.ker = N) (Z : (X ⧸ N) →L[ℂ] Y)
    (hZ : ∀ x, Z (N.mkQ x) = T x) : IsClosedEmbedding Z := by
  have hq : IsQuotientMap T.rangeRestrict :=
    ho.isQuotientMap T.rangeRestrict.continuous T.toLinearMap.surjective_rangeRestrict
  have hker : T.rangeRestrict.ker = N := by
    rw [← hk]
    ext x
    change T.rangeRestrict x = 0 ↔ T x = 0
    rw [Subtype.ext_iff]
    rfl
  exact exists_polarThetaNuclearityAction_closedEmbedding_of_factor N T.rangeRestrict hq
    hker T.range.subtypeL hc.isClosedEmbedding_subtypeVal Z hZ

/-- The polar theta Mellin map is a closed embedding on every norm-one component. -/
private theorem exists_polarThetaNuclearityAction_mellin_closedEmbedding
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F)) :
    IsClosedEmbedding (exists_globalPolarThetaMellin χ τ hτ).choose := by
  let ω : PontryaginDual (ideleClassNorm F).ker := χ.comp
    (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
      (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)
  let P₀ := adelePolarSubspace F
  let θ := homogeneousAdelicThetaLinearMap F ω
  let N := (θ.domRestrict P₀).ker
  let Z := (exists_globalPolarThetaMellin χ τ hτ).choose
  have hZ (f : P₀) (s : ℂ) : (Z (N.mkQ f)).val s =
      globalIdelicZFunction f.val (ideleClassNormTwist χ s) :=
    ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f s).2
  by_cases hω : ω = 1
  · obtain ⟨t, ht, _⟩ := globalConverse_existsUnique_normTwist χ hω
    obtain ⟨T, ho, hc, hT, _, hk⟩ := globalConverse_normTwist χ t ht
    have hker : T.ker = N := by
      rw [hk]
      dsimp only [N, θ]
      rw [hω]
      rfl
    apply exists_polarThetaNuclearityAction_closedEmbedding_of_range N T ho hc hker Z
    intro f
    exact Subtype.ext (funext fun s ↦ (hZ f s).trans (hT f s).symm)
  · obtain ⟨j, hj, hje, _⟩ := globalConverse_nontrivial χ hω
    let q : P₀ →L[ℂ] (SchwartzBruhat (Multiplicative 𝔸[F]) ⧸ θ.ker) :=
      θ.ker.mkQL.comp P₀.subtypeL
    have hq : IsQuotientMap q := (globalConverse_nontrivial_exact ω hω).isQuotientMap
    have hqker : q.ker = N := by
      ext f
      change θ.ker.mkQ f.val = 0 ↔ θ f.val = 0
      exact Submodule.Quotient.mk_eq_zero θ.ker
    apply exists_polarThetaNuclearityAction_closedEmbedding_of_factor N q hq hqker j hj Z
    intro f
    exact Subtype.ext (funext fun s ↦ (hZ f s).trans (hje f.val s).symm)

/-- A continuous endomorphism preserving the range of a topological linear
embedding transports to a continuous endomorphism of its source. -/
private theorem exists_polarThetaNuclearityAction_conjugate
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (Z : X →L[ℂ] Y) (hZ : IsEmbedding Z) (T : Y →L[ℂ] Y)
    (hT : Set.MapsTo T (Set.range Z) (Set.range Z)) :
    ∃ A : X →L[ℂ] X, ∀ x, Z (A x) = T (Z x) := by
  let e₀ := LinearEquiv.ofInjective Z.toLinearMap hZ.injective
  have he₀ (y : Z.range) : Z (e₀.symm y) = y.val :=
    congrArg Subtype.val (e₀.apply_symm_apply y)
  let e : X ≃L[ℂ] Z.range :=
    { e₀ with
      continuous_toFun := Z.rangeRestrict.continuous
      continuous_invFun := hZ.continuous_iff.mpr
        (show Continuous (Z ∘ e₀.symm) from
          continuous_subtype_val.congr fun y ↦ (he₀ y).symm) }
  let R : Z.range →L[ℂ] Z.range :=
    (T.comp Z.range.subtypeL).codRestrict Z.range (fun y ↦ hT y.property)
  let A := e.symm.toContinuousLinearMap.comp (R.comp e.toContinuousLinearMap)
  exact ⟨A, fun x ↦ he₀ (R (e x))⟩


/-- Continuous integrable functions are determined pointwise by their Fourier transforms. -/
private theorem exists_polarThetaNuclearityAction_eq_of_fourier_eq
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (f g : G → ℂ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfc : Continuous f) (hgc : Continuous g)
    (he : ∀ ψ : PontryaginDual G, lcaFourier μ f ψ = lcaFourier μ g ψ) : f = g := by
  obtain ⟨Φ, hΦ, hinj, -⟩ := lcaFourier_L1 (G := G) μ
  have hcoe (w : G → ℂ) (hw : Integrable w μ) (ψ : PontryaginDual G) :
      Φ (hw.toL1 w) ψ = lcaFourier μ w ψ := by
    rw [hΦ]
    exact integral_congr_ae (hw.coeFn_toL1.mono fun y hy ↦
      congrArg (· * star (ψ y : ℂ)) hy)
  have hL1 : hf.toL1 f = hg.toL1 g :=
    hinj (ZeroAtInftyContinuousMap.ext fun ψ ↦ by rw [hcoe, hcoe, he])
  exact (hfc.ae_eq_iff_eq μ hgc).mp ((Integrable.toL1_eq_toL1_iff f g hf hg).mp hL1)

/-- A Fourier coefficient vanishes when its character does not match the translation isotype. -/
private theorem exists_polarThetaNuclearityAction_fourier_zero_off_isotype
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (K : Subgroup G) (ω : PontryaginDual K) (f : G → ℂ)
    (hh : ∀ h : K, ∀ x, f (h.val⁻¹ * x) = (ω h : ℂ) * f x)
    (ψ : PontryaginDual G) (h : K) (hne : star (ψ h.val : ℂ) ≠ (ω h : ℂ)) :
    lcaFourier μ f ψ = 0 := by
  have htrans : lcaFourier μ (fun x ↦ f (h.val⁻¹ * x)) ψ =
      star (ψ h.val : ℂ) * lcaFourier μ f ψ := by
    unfold lcaFourier
    rw [← integral_mul_left_eq_self (μ := μ)
      (fun x ↦ f (h.val⁻¹ * x) * star (ψ x : ℂ)) h.val, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      simp only [inv_mul_cancel_left, map_mul, Circle.coe_mul, star_mul]
      ring
  have hiso : lcaFourier μ (fun x ↦ f (h.val⁻¹ * x)) ψ =
      (ω h : ℂ) * lcaFourier μ f ψ := by
    unfold lcaFourier
    simp_rw [hh h, mul_assoc]
    exact integral_const_mul _ _
  have he : ((ω h : ℂ) - star (ψ h.val : ℂ)) * lcaFourier μ f ψ = 0 := by
    rw [sub_mul, sub_eq_zero]
    exact hiso.symm.trans htrans
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne.symm)

/-- For functions of one isotype, it suffices to compare the Fourier transforms on that component. -/
private theorem exists_polarThetaNuclearityAction_eq_convolution_of_component_fourier
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (K : Subgroup G) (ω : PontryaginDual K) (φ f g : G → ℂ)
    (hφ : Integrable φ μ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hgc : Continuous g) (hcc : Continuous (lcaConvolution μ φ f))
    (hfh : ∀ h : K, ∀ x, f (h.val⁻¹ * x) = (ω h : ℂ) * f x)
    (hgh : ∀ h : K, ∀ x, g (h.val⁻¹ * x) = (ω h : ℂ) * g x)
    (hformula : ∀ ψ : PontryaginDual G,
      (∀ h : K, star (ψ h.val : ℂ) = (ω h : ℂ)) →
      lcaFourier μ g ψ = lcaFourier μ φ ψ * lcaFourier μ f ψ) :
    g = lcaConvolution μ φ f := by
  apply exists_polarThetaNuclearityAction_eq_of_fourier_eq μ g (lcaConvolution μ φ f) hg
    (lcaConvolution_integrable μ hφ hf).2.1 hgc hcc
  intro ψ
  rw [lcaFourier_convolution μ hφ hf, Pi.mul_apply]
  by_cases hh : ∀ h : K, star (ψ h.val : ℂ) = (ω h : ℂ)
  · exact hformula ψ hh
  · obtain ⟨h, hne⟩ := not_forall.mp hh
    rw [exists_polarThetaNuclearityAction_fourier_zero_off_isotype μ K ω g hgh ψ h hne,
      exists_polarThetaNuclearityAction_fourier_zero_off_isotype μ K ω f hfh ψ h hne, mul_zero]

/-- Convolving a continuous function with a continuous compactly supported test is continuous. -/
private theorem exists_polarThetaNuclearityAction_convolution_continuous
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (φ f : G → ℂ) (hφ : Continuous φ) (hf : Continuous f)
    (hφc : HasCompactSupport φ) : Continuous (lcaConvolution μ φ f) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (μ := μ) (k := tsupport φ) hφc
  · exact ((hφ.comp continuous_snd).mul
      (hf.comp ((continuous_snd.inv).mul continuous_fst))).continuousOn
  · intro x y _ hy
    simp [image_eq_zero_of_notMem_tsupport hy]


/-- The Fourier characters of a fixed component are norm twists of the chosen unitary character. -/
private theorem exists_polarThetaNuclearityAction_character_component
    {F : Type*} [Field F] [NumberField F]
    (χ ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (hψ : ∀ h : (ideleClassNorm F).ker, star (ψ h.val : ℂ) = (χ h.val : ℂ)) :
    ∃ s : ℂ, s.re = 2 ∧ ∀ x : IdeleClassGroup (𝓞 F) F,
      ((((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ) ^ (2 : ℕ)) * star (ψ x : ℂ) =
        ideleClassNormTwist χ s x := by
  let η : PontryaginDual (IdeleClassGroup (𝓞 F) F) := ψ⁻¹ * χ⁻¹
  have hη : η.comp
      (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F) = 1 := by
    apply PontryaginDual.ext
    intro h
    change (ψ h.val)⁻¹ * (χ h.val)⁻¹ = 1
    have hh : (ψ h.val)⁻¹ = χ h.val := by
      apply Circle.ext
      rw [Circle.coe_inv_eq_conj, ← Complex.star_def]
      exact hψ h
    rw [hh, mul_inv_cancel]
  obtain ⟨t, ht, -⟩ := globalConverse_existsUnique_normTwist η hη
  have hval (ξ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (z : ℂ)
      (x : IdeleClassGroup (𝓞 F) F) : ideleClassNormTwist ξ z x =
      (ξ x : ℂ) * ((((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ) ^ z) := rfl
  have hchar (x : IdeleClassGroup (𝓞 F) F) : star (ψ x : ℂ) =
      (χ x : ℂ) * ((((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) := by
    have hx := DFunLike.congr_fun ht x
    rw [hval, hval, Complex.cpow_zero, mul_one, PontryaginDual.one_apply,
      Circle.coe_one, one_mul] at hx
    change (((ψ x)⁻¹ * (χ x)⁻¹ : Circle) : ℂ) = _ at hx
    rw [Circle.coe_mul, Circle.coe_inv_eq_conj (ψ x), ← Complex.star_def,
      Circle.coe_inv] at hx
    have hh := congrArg (fun z : ℂ ↦ z * (χ x : ℂ)) hx
    simp only [mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero (χ x)), mul_one] at hh
    exact hh.trans (mul_comm _ _)
  refine ⟨2 + (t : ℂ) * Complex.I, by simp, fun x ↦ ?_⟩
  have hn : ((((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (ideleClassNorm F x).ne_zero)
  rw [hval, Complex.cpow_add _ _ hn, Complex.cpow_ofNat, hchar]
  ring


/-- Multiplicative weights commute with convolution. -/
private theorem exists_polarThetaNuclearityAction_weight_convolution
    {G : Type*} [CommGroup G] [MeasurableSpace G] (μ : Measure G)
    (c : G →* ℂ) (φ f : G → ℂ) (x : G) :
    lcaConvolution μ (fun y ↦ c y * φ y) (fun y ↦ c y * f y) x =
      c x * lcaConvolution μ φ f x := by
  unfold lcaConvolution
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  have hc : c y * c (y⁻¹ * x) = c x := by
    rw [← map_mul, mul_inv_cancel_left]
  calc
    (c y * φ y) * (c (y⁻¹ * x) * f (y⁻¹ * x)) =
        (c y * c (y⁻¹ * x)) * (φ y * f (y⁻¹ * x)) := by ring
    _ = c x * (φ y * f (y⁻¹ * x)) := by rw [hc]

/-- The squared norm weight makes a homogeneous theta function integrable on the full class group. -/
private theorem exists_polarThetaNuclearityAction_weighted_integrable
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) :
    let ω : PontryaginDual (ideleClassNorm F).ker := χ.comp
      (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)
    Integrable (fun x ↦ ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 2 x *
      homogeneousAdelicTheta ω f x) (ideleClassTamagawaMeasure F) := by
  intro ω
  let : BorelSpace (IdeleClassGroup (𝓞 F) F) := ⟨rfl⟩
  let c := ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (2 : ℂ)
  have h := (homogeneousTheta_classMellin_eq_mass_mul χ f ⟨2, by norm_num⟩).1
  have he (x : IdeleClassGroup (𝓞 F) F) :
      homogeneousAdelicTheta ω f x * ideleClassNormTwist χ 2 x =
        (χ x : ℂ) * (c x * homogeneousAdelicTheta ω f x) := by
    change homogeneousAdelicTheta ω f x * ((χ x : ℂ) *
        ((((ideleClassNorm F x).val : ℝ) : ℂ) ^ (2 : ℂ))) =
      (χ x : ℂ) * ((1 * ((((ideleClassNorm F x).val : ℝ) : ℂ) ^ (2 : ℂ))) *
        homogeneousAdelicTheta ω f x)
    ring
  apply h.mono ((c.continuous.mul (homogeneousAdelicTheta_continuous ω f)).aestronglyMeasurable)
  filter_upwards with x
  change ‖c x * homogeneousAdelicTheta ω f x‖ ≤
    ‖homogeneousAdelicTheta ω f x * ideleClassNormTwist χ 2 x‖
  simp only [he, norm_mul, Circle.norm_coe, one_mul, le_refl]


/-- A compactly supported Bruhat test is continuous, by its zero twist in the decay space. -/
private theorem exists_polarThetaNuclearityAction_test_continuous
    (F : Type*) [Field F] [NumberField F]
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) : Continuous φ.val := by
  let m : IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ :=
    (continuousIdeleClassNorm F)
  have hm : IsModulation m := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hms : Surjective m := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  let d := bruhatCompactSupportToModulatedExponentialDecay m univ hm hms φ
  let f := modulatedExponentialDecayTwist m univ ⟨0, mem_univ (0 : ℝ)⟩ d
  have he : (f : IdeleClassGroup (𝓞 F) F → ℂ) = φ.val := modulationWeight_zero m φ.val
  exact (schwartzBruhat_continuous f).congr (congrFun he)

/-- Mellin multiplication identifies the theta representative of the transported operator with Haar convolution. -/
private theorem exists_polarThetaNuclearityAction_convolution_graph
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
    (f g : adelePolarSubspace F)
    (hM : ∀ s : ℂ,
      globalIdelicZFunction g.val (ideleClassNormTwist χ s) =
        nuclearityTestMellin χ φ s * globalIdelicZFunction f.val (ideleClassNormTwist χ s)) :
    (homogeneousAdelicTheta
      (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)) g.val :
      IdeleClassGroup (𝓞 F) F → ℂ) =
    lcaConvolution (ideleClassTamagawaMeasure F) φ.val (homogeneousAdelicTheta
      (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)) f.val) := by
  let G := IdeleClassGroup (𝓞 F) F
  let μ := ideleClassTamagawaMeasure F
  let K := (ideleClassNorm F).ker
  let ω : PontryaginDual (ideleClassNorm F).ker := χ.comp (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)
  let c := ideleClassNormTwist (1 : PontryaginDual G) (2 : ℂ)
  let Hf : G → ℂ := homogeneousAdelicTheta ω f.val
  let Hg : G → ℂ := homogeneousAdelicTheta ω g.val
  let weightedF : G → ℂ := fun x ↦ c x * Hf x
  let weightedG : G → ℂ := fun x ↦ c x * Hg x
  let Pφ : G → ℂ := fun x ↦ c x * φ.val x
  let mass : ℂ := ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ)
  let : BorelSpace G := ⟨rfl⟩
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let : μ.Regular := (ideleClassTamagawaMeasure_isWeil F).2.1
  have hφc : Continuous φ.val := exists_polarThetaNuclearityAction_test_continuous F φ
  have hPc : Continuous Pφ := c.continuous.mul hφc
  have hPs : HasCompactSupport Pφ :=
    (show HasCompactSupport φ.val from φ.property.2).mul_left
  have hPi : Integrable Pφ μ := hPc.integrable_of_hasCompactSupport hPs
  have hUi : Integrable weightedF μ := exists_polarThetaNuclearityAction_weighted_integrable F χ f.val
  have hVi : Integrable weightedG μ := exists_polarThetaNuclearityAction_weighted_integrable F χ g.val
  have hUc : Continuous weightedF := c.continuous.mul (homogeneousAdelicTheta_continuous ω f.val)
  have hVc : Continuous weightedG := c.continuous.mul (homogeneousAdelicTheta_continuous ω g.val)
  have hcK (h : K) : c h.val = 1 := by
    change (1 : ℂ) * (((ideleClassNorm F h.val).val : ℂ) ^ (2 : ℂ)) = 1
    rw [MonoidHom.mem_ker.mp h.property]
    simp
  have hiso (u : SchwartzBruhat (Multiplicative 𝔸[F])) (h : K) (x : G) :
      c (h.val⁻¹ * x) * homogeneousAdelicTheta ω u (h.val⁻¹ * x) =
        (ω h : ℂ) * (c x * homogeneousAdelicTheta ω u x) := by
    rw [map_mul, map_inv, hcK, inv_one, one_mul]
    exact (congrArg (c x * ·) (homogeneousAdelicTheta_homogeneous ω u h x)).trans
      (mul_left_comm _ _ _)
  have hEq : weightedG = lcaConvolution μ Pφ weightedF := by
    apply exists_polarThetaNuclearityAction_eq_convolution_of_component_fourier μ K ω Pφ weightedF weightedG hPi hUi hVi hVc
      (exists_polarThetaNuclearityAction_convolution_continuous μ Pφ weightedF hPc hUc hPs)
      (hiso f.val) (hiso g.val)
    intro ψ hψ
    obtain ⟨s, hs, hcs₀⟩ := exists_polarThetaNuclearityAction_character_component χ ψ hψ
    have hcs (x : G) : c x * star (ψ x : ℂ) = ideleClassNormTwist χ s x := by
      change (1 * (((((ideleClassNorm F x).val : ℝ) : ℂ)) ^ (2 : ℂ))) *
        star (ψ x : ℂ) = _
      rw [one_mul, Complex.cpow_ofNat]
      exact hcs₀ x
    have hF (u : SchwartzBruhat (Multiplicative 𝔸[F])) :
        lcaFourier μ (fun x ↦ c x * homogeneousAdelicTheta ω u x) ψ =
          mass * globalIdelicZFunction u (ideleClassNormTwist χ s) := by
      apply (integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)).trans
        (homogeneousTheta_classMellin_eq_mass_mul χ u ⟨s, by change 1 < s.re; rw [hs]; norm_num⟩).2
      change (c x * homogeneousAdelicTheta ω u x) * star (ψ x : ℂ) =
        homogeneousAdelicTheta ω u x * ideleClassNormTwist χ s x
      rw [← hcs]
      ring
    have hP : lcaFourier μ Pφ ψ = nuclearityTestMellin χ φ s := by
      apply integral_congr_ae
      filter_upwards with x
      change (c x * φ.val x) * star (ψ x : ℂ) = φ.val x * ideleClassNormTwist χ s x
      rw [← hcs]
      ring
    rw [hF, hF, hP, hM]
    ring
  funext x
  have hh := congrFun hEq x
  have hh' : c x * Hg x = c x * lcaConvolution μ φ.val Hf x :=
    hh.trans (exists_polarThetaNuclearityAction_weight_convolution μ c.toMonoidHom φ.val Hf x)
  have hcne : c x ≠ 0 := by
    intro hz
    have hp : c x * c x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [hz, zero_mul] at hp
    exact zero_ne_one hp
  exact mul_left_cancel₀ hcne hh'


/-- A map on a quotient has the prescribed graph once it has that graph on representatives. -/
private theorem exists_polarThetaNuclearityAction_graph_iff
    {Test Q Y : Type*} (q : Test → Q) (H : Test → Y) (C : Y → Y) (A : Q → Q)
    (hq : Function.Surjective q) (hker : ∀ f g, q f = q g ↔ H f = H g)
    (hforward : ∀ f g, A (q f) = q g → H g = C (H f)) :
    ∀ f g, A (q f) = q g ↔ H g = C (H f) := by
  intro f g
  constructor
  · exact hforward f g
  · intro h
    obtain ⟨u, hu⟩ := hq (A (q f))
    have huH := hforward f u hu.symm
    exact hu.symm.trans ((hker u g).mpr (huH.trans h.symm))

/-- Classes modulo a linear kernel agree exactly when the linear images agree. -/
private theorem exists_polarThetaNuclearityAction_quotient_eq_iff
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (T : X →ₗ[ℂ] Y) (f g : X) :
    T.ker.mkQ f = T.ker.mkQ g ↔ T f = T g := by
  change (Submodule.Quotient.mk f : X ⧸ T.ker) = Submodule.Quotient.mk g ↔ _
  rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]

/-- The convolution identity on representatives gives the graph of the quotient action. -/
private theorem exists_polarThetaNuclearityAction_graph_of_mellin
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : Function.RightInverse τ (ideleNorm F))
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) :
    let ω : PontryaginDual (ideleClassNorm F).ker := χ.comp
      (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)
    let P₀ := adelePolarSubspace F
    let T := (homogeneousAdelicThetaLinearMap F ω).domRestrict P₀
    let N := T.ker
    let Z := (exists_globalPolarThetaMellin χ τ hτ).choose
    ∀ A : (P₀ ⧸ N) →L[ℂ] (P₀ ⧸ N),
      (∀ x s, (Z (A x)).val s = nuclearityTestMellin χ φ s * (Z x).val s) →
      ∀ f g : P₀, A (N.mkQ f) = N.mkQ g ↔
        (homogeneousAdelicTheta ω g.val : IdeleClassGroup (𝓞 F) F → ℂ) =
          lcaConvolution (ideleClassTamagawaMeasure F) φ.val (homogeneousAdelicTheta ω f.val) := by
  intro ω P₀ T N Z A hA
  let H (f : P₀) : IdeleClassGroup (𝓞 F) F → ℂ := homogeneousAdelicTheta ω f.val
  have hZ (f : P₀) (s : ℂ) : (Z (N.mkQ f)).val s =
      globalIdelicZFunction f.val (ideleClassNormTwist χ s) :=
    ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f s).2
  have hquot (f g : P₀) : N.mkQ f = N.mkQ g ↔ H f = H g := by
    rw [exists_polarThetaNuclearityAction_quotient_eq_iff T f g]
    constructor
    · intro h
      exact congrArg (fun k : C(IdeleClassGroup (𝓞 F) F, ℂ) ↦
        (k : IdeleClassGroup (𝓞 F) F → ℂ)) h
    · intro h
      exact ContinuousMap.ext (congrFun h)
  apply exists_polarThetaNuclearityAction_graph_iff N.mkQ H
    (fun h ↦ lcaConvolution (ideleClassTamagawaMeasure F) φ.val h) A N.mkQ_surjective hquot
  intro f g hfg
  apply exists_polarThetaNuclearityAction_convolution_graph F χ φ f g
  intro s
  calc
    globalIdelicZFunction g.val (ideleClassNormTwist χ s) = (Z (N.mkQ g)).val s :=
      (hZ g s).symm
    _ = (Z (A (N.mkQ f))).val s :=
      congrArg (fun x ↦ (Z x).val s) hfg.symm
    _ = nuclearityTestMellin χ φ s * (Z (N.mkQ f)).val s := hA (N.mkQ f) s
    _ = nuclearityTestMellin χ φ s *
        globalIdelicZFunction f.val (ideleClassNormTwist χ s) := by rw [hZ]

/-- Paper: Theorem 7.4.2.1(1)–(2), p. 367, and Theorem 7.4.3.2, pp. 372–373.
In global Mellin coordinates the regularized theta action is multiplication by
the transform of the test. The induced map on theta functions is Haar convolution. -/
theorem exists_polarThetaNuclearityAction (φ : 𝒟) :
    ∃ A : Θ₀(χ) →L[ℂ] Θ₀(χ),
      (∀ f s, ((Z(χ, τ, hτ)) (A f)).val s =
        nuclearityTestMellin χ φ s * ((Z(χ, τ, hτ)) f).val s) ∧
      ∀ f g : P, A mkΘ(χ, f) = mkΘ(χ, g) ↔
        (homogeneousAdelicTheta (ω(χ)) g.val : C𝔽 → ℂ) =
          lcaConvolution μ𝔽 φ.val (homogeneousAdelicTheta (ω(χ)) f.val) := by
  let Z := (exists_globalPolarThetaMellin χ τ hτ).choose
  obtain ⟨_, T, hT, hPres⟩ := spectralNuclearityDenominator_closed_invariant χ τ hτ 0 φ
  have hz := exists_polarThetaNuclearityAction_mellin_closedEmbedding F χ τ hτ
  have hPres' : Set.MapsTo T (Set.range Z) (Set.range Z) := by
    change Set.MapsTo T (Z.toLinearMap.range : Set (SchwartzBergman univ))
      (Z.toLinearMap.range : Set (SchwartzBergman univ))
    rw [← spectralNuclearityDenominator_zero χ τ hτ]
    exact hPres
  obtain ⟨A, hA⟩ := exists_polarThetaNuclearityAction_conjugate Z hz.isEmbedding T hPres'
  have hM : ∀ f s, (Z (A f)).val s = nuclearityTestMellin χ φ s * (Z f).val s :=
    fun f s ↦ (congrArg (fun b ↦ b.val s) (hA f)).trans (hT (Z f) s)
  exact ⟨A, hM, exists_polarThetaNuclearityAction_graph_of_mellin F χ τ hτ φ A hM⟩

local notation "Aθ(" φ ")" => (exists_polarThetaNuclearityAction χ τ hτ φ).choose

/-- Paper: Equation (7.4.0.2), p. 366.
The finite places of a number field lying above one rational prime form a finite set. -/
theorem finite_nuclearityPlacesAbove (p : HeightOneSpectrum (𝓞 ℚ)) :
    {v : V | v.under (𝓞 ℚ) = p}.Finite := by
  apply Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
    (hi := HeightOneSpectrum.asIdeal_injective.injOn)
  apply (IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 F)).subset
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (show w.under (𝓞 ℚ) = p from hw).symm⟩⟩

local notation "Sₚ(" p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset

/-- Paper: Equation (7.4.0.2), p. 366.
Principal value preserves the common kernel of the two global polar evaluations. -/
theorem nuclearityPrincipalValue_mem_polar (p : HeightOneSpectrum (𝓞 ℚ)) (f : P) :
    adelePrincipalValue F (Sₚ(p)) f.val ∈ P := by
  classical
  have hn : (Sₚ(p)).Nonempty := by
    have := p.isMaximal
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) p.asIdeal
    let v : V := ⟨q, hq.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot q⟩
    exact ⟨v, (finite_nuclearityPlacesAbove p).mem_toFinset.mpr (HeightOneSpectrum.ext hqp.over.symm)⟩
  let E := SchwartzBruhat (Multiplicative 𝔸[F])
  let pv : E →L[ℂ] E :=
    ⟨adelePrincipalValue F (Sₚ(p)), (adelePrincipalValue_isClosedEmbedding (Sₚ(p))).continuous⟩
  let vals : E →L[ℂ] ℂ × ℂ := ⟨adelePolarValues, adelePolarValues_continuous⟩
  obtain ⟨y, hy⟩ := adelePolarValues_surjective (F := F) ((1, 1) : ℂ × ℂ)
  change vals y = (1, 1) at hy
  have hx : vals f.val = 0 := f.property
  -- Pullback by principal value preserves the eigenspace of each polar functional.
  have coord (L : ℂ × ℂ →L[ℂ] ℂ) (c : QuasiCharacter C𝔽)
      (hL : L.comp vals ∈ adelicEigendistributions c) (h1 : L (1, 1) = 1) :
      L (vals (pv f.val)) = 0 := by
    let l := L.comp vals
    have hk : l.comp pv ∈ adelicEigendistributions c := by
      intro u t
      have he := congrArg (fun q : GlobalAdelicThetaSpace F ↦ L (globalThetaPolarValues q))
        (globalThetaPrincipalValue_equivariant hn u t)
      exact he.trans (hL u (pv t))
    have hl : l ≠ 0 := by
      intro hz
      have hy' : l y = 1 := (congrArg L hy).trans h1
      rw [hz] at hy'
      exact zero_ne_one hy'
    have hdim := Module.rank_eq_one_iff_finrank_eq_one.mp (adelicEigendistributions_rank c)
    rw [eq_span_singleton_of_mem_of_finrank_eq_one hdim hL hl, Submodule.mem_span_singleton] at hk
    obtain ⟨a, ha⟩ := hk
    have he := congrArg (fun k : E →L[ℂ] ℂ ↦ k f.val) ha.symm
    change L (vals (pv f.val)) = a * L (vals f.val) at he
    simpa only [hx, map_zero, mul_zero] using he
  apply (mem_adelePolarSubspace _).2
  constructor
  · apply coord (ContinuousLinearMap.fst ℂ ℂ ℂ) 1 _ rfl
    intro u t
    change t (Multiplicative.ofAdd ((↑u⁻¹ : 𝔸[F]) * 0)) = 1 * t (Multiplicative.ofAdd 0)
    rw [mul_zero, one_mul]
  · apply coord (ContinuousLinearMap.snd ℂ ℂ ℂ) (ideleClassNormTwist (1 : U) 1) _ rfl
    intro u t
    have h := globalThetaPolarValues_snd_translate (QuotientGroup.mk u) (Submodule.Quotient.mk t)
    rw [(existsUnique_globalThetaAction (F := F)).exists.choose_spec.2 u t] at h
    change (adelePolarValues (schwartzBruhatUnitTranslate u t)).2 =
      ((1 : ℂ) * (((ideleNorm F u).val : ℝ) : ℂ) ^ (1 : ℂ)) * (adelePolarValues t).2
    rw [Complex.cpow_one, one_mul]
    exact h

/-- Paper: Equation (7.4.0.2), p. 366.
The finite-place denominator is the theta image of principal values of zero-moment
tests, with the principal value taken at all places above the rational prime. -/
def finiteNuclearityDenominator (p : HeightOneSpectrum (𝓞 ℚ)) : Submodule ℂ (Θ₀(χ)) :=
  Submodule.span ℂ (Set.range (fun f : P ↦
    (Submodule.Quotient.mk ⟨adelePrincipalValue F (Sₚ(p)) f.val,
      nuclearityPrincipalValue_mem_polar (F := F) p f⟩ : Θ₀(χ))))

/-- Paper: Equation (7.4.0.2), p. 366.
The finite orbital quotient is taken by the principal-value image.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its definition (#5398). -/
def FiniteNuclearityQuotient (p : HeightOneSpectrum (𝓞 ℚ)) :=
  Θ₀(χ) ⧸ finiteNuclearityDenominator χ p

namespace FiniteNuclearityQuotient

instance instAddCommGroup (p : HeightOneSpectrum (𝓞 ℚ)) :
    AddCommGroup (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (AddCommGroup (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

instance instModule (p : HeightOneSpectrum (𝓞 ℚ)) : Module ℂ (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (Module ℂ (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

instance instTopologicalSpace (p : HeightOneSpectrum (𝓞 ℚ)) :
    TopologicalSpace (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (TopologicalSpace (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

instance instIsTopologicalAddGroup (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsTopologicalAddGroup (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (IsTopologicalAddGroup (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

instance instContinuousSMul (p : HeightOneSpectrum (𝓞 ℚ)) :
    ContinuousSMul ℂ (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (ContinuousSMul ℂ (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

end FiniteNuclearityQuotient

private theorem mkQ_span_range_eq_zero {E M : Type*} [AddCommGroup E] [AddCommGroup M]
    [Module ℂ E] [Module ℂ M] (L : E →ₗ[ℂ] M) (x : M) :
    (Submodule.span ℂ (Set.range L)).mkQ x = 0 ↔ ∃ y, x = L y := by
  have hle : Submodule.span ℂ (Set.range L) ≤ LinearMap.range L :=
    Submodule.span_le.mpr Set.Subset.rfl
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hle hx
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, hy⟩
    exact Submodule.subset_span ⟨y, hy.symm⟩

private theorem mkQ_principal_range_eq_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (S : Submodule ℂ E) (Q : Submodule ℂ S) (A : E →ₗ[ℂ] E)
    (h : ∀ g : S, A g.val ∈ S) (f : S) :
    (Submodule.span ℂ (Set.range (fun g : S ↦
      (Submodule.Quotient.mk ⟨A g.val, h g⟩ : S ⧸ Q)))).mkQ
        (Submodule.Quotient.mk f) = 0 ↔
      ∃ g : S, (Submodule.Quotient.mk f : S ⧸ Q) = Submodule.Quotient.mk ⟨A g.val, h g⟩ :=
  mkQ_span_range_eq_zero (Q.mkQ.comp ((A.domRestrict S).codRestrict S h)) (Q.mkQ f)

/-- Paper: Equation (7.4.0.2), p. 366.
The class of a test is zero in the finite quotient exactly when its theta class
is represented by a principal value. -/
theorem finiteNuclearityQuotient_mk_eq_zero (p : HeightOneSpectrum (𝓞 ℚ)) (f : P) :
    (finiteNuclearityDenominator χ p).mkQ mkΘ(χ, f) = 0 ↔
      ∃ g : P, mkΘ(χ, f) =
        mkΘ(χ, ⟨adelePrincipalValue F (Sₚ(p)) g.val, nuclearityPrincipalValue_mem_polar (F := F) p g⟩) :=
  by
    unfold finiteNuclearityDenominator
    have hz := mkQ_principal_range_eq_zero P (Π(χ)) (adelePrincipalValue F (Sₚ(p)))
      (nuclearityPrincipalValue_mem_polar (F := F) p) f
    with_reducible exact hz

/-- The polar Mellin transform separates homogeneous theta classes by the two
global converse theorems, using their respective kernels. -/
private theorem finiteNuclearity_mellin_injective : Injective (Z(χ, τ, hτ)) := by
  apply LinearMap.ker_eq_bot.mp
  refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (Π(χ)) x
  have hZ : (Z(χ, τ, hτ)) (mkΘ(χ, f)) = 0 := hx
  have hf (s : ℂ) : globalIdelicZFunction f.val (ideleClassNormTwist χ s) = 0 := by
    rw [← ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f s).2, hZ]
    rfl
  apply (Submodule.Quotient.mk_eq_zero (Π(χ))).mpr
  by_cases hω : ω(χ) = 1
  · obtain ⟨t, ht⟩ := (globalConverse_existsUnique_normTwist χ hω).exists
    obtain ⟨M, _, _, hM, _, hker⟩ := globalConverse_normTwist χ t ht
    have hm : f ∈ M.ker := specDenom_B_ext (M f) 0 (fun s ↦ (hM f s).trans (hf s))
    have hK := congrArg (fun ψ ↦ (homogeneousAdelicThetaLinearMap F ψ).ker.comap (P).subtype) hω
    exact (hK.trans hker.symm).ge hm
  · obtain ⟨M, hM, hval, _⟩ := globalConverse_nontrivial χ hω
    let K := (homogeneousAdelicThetaLinearMap F (ω(χ))).ker
    have hfM : M (K.mkQ f.val) = 0 :=
      specDenom_B_ext _ 0 (fun s ↦ (hval f.val s).trans (hf s))
    change f.val ∈ K
    exact (Submodule.Quotient.mk_eq_zero K).mp (hM.injective (hfM.trans M.map_zero.symm))

local notation "orbitalGenerator(" S ")" => orbitalHeckeGenerator χ τ hτ
  (continuedCompletedHeckeL χ) (continuedCompletedHeckeL_spec χ).1
  (continuedCompletedHeckeL_spec χ).2 S

/-- A surjective choice of representatives carries a Mellin range equality
to a pointwise description on those representatives. -/
private theorem finiteNuclearity_values_of_range {X Y C : Type*} (q : X → Y)
    (hq : Surjective q) (M : Y → C) (ev : C → ℂ → ℂ) (g : ℂ → ℂ)
    (hM : Set.range M = {b | ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev b s = g s * u s})
    (hev : Injective ev) (val : X → ℂ → ℂ) (hval : ∀ x s, ev (M (q x)) s = val x s) (b : C) :
    (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev b s = g s * u s) ↔
      ∃ x, ∀ s, ev b s = val x s := by
  have hr : b ∈ Set.range M ↔ ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev b s = g s * u s :=
    Set.ext_iff.mp hM b
  refine hr.symm.trans ?_
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨x, hval x⟩
  · rintro ⟨x, hx⟩
    exact ⟨q x, hev (funext fun s ↦ (hval x s).trans (hx s).symm)⟩

open Classical in
private theorem finiteNuclearity_mellin_values_normTwist (S : Finset V) (b : B)
    (hω : ω(χ) = 1) :
    (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, b.val s = (orbitalGenerator(S)).val s * u s) ↔
      ∃ f : P, ∀ s : ℂ, b.val s =
        globalIdelicZFunction (adelePrincipalValue F S f.val) (ideleClassNormTwist χ s) := by
  let L := fun s : ℂ ↦ (orbitalGenerator(S)).val s
  let ev := fun b : B ↦ b.val
  let val (f : P) (s : ℂ) :=
    globalIdelicZFunction (adelePrincipalValue F S f.val) (ideleClassNormTwist χ s)
  have hev : Injective ev := Subtype.val_injective
  change (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, b.val s = L s * u s) ↔ ∃ f, ∀ s, ev b s = val f s
  obtain ⟨t, ht⟩ := (globalConverse_existsUnique_normTwist χ hω).exists
  obtain ⟨M, _, _, hM, hRange, _⟩ := globalPrincipalValueConverse_normTwist S χ t ht
  let W := (P).map (adelePrincipalValue F S)
  let q : P → W := fun f ↦ ⟨adelePrincipalValue F S f.val, Submodule.mem_map_of_mem f.property⟩
  have hq : Surjective q := by
    intro y
    obtain ⟨f, hf, hfy⟩ := y.property
    exact ⟨⟨f, hf⟩, Subtype.ext hfy⟩
  have hL : L = fun s ↦ reciprocalPartialHeckeEulerProduct χ S s *
      toMeromorphicNFOn (fun s ↦ ((s + (t : ℂ) * Complex.I) *
        (1 - s - (t : ℂ) * Complex.I)) * continuedCompletedHeckeL χ s) univ s := by
    funext s
    change reciprocalPartialHeckeEulerProduct χ S s *
      (regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
        (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2).val s = _
    rw [congrFun (specDenom_L1 χ τ hτ t hω ht) s]
  rw [hL]
  have heq (f : P) (s : ℂ) : (M (q f)).val s =
      globalIdelicZFunction (adelePrincipalValue F S f.val) (ideleClassNormTwist χ s) :=
    hM (q f) s
  with_reducible exact finiteNuclearity_values_of_range q hq M ev _ hRange hev val heq b

open Classical in
private theorem finiteNuclearity_mellin_values_nontrivial (S : Finset V) (b : B)
    (hω : ω(χ) ≠ 1) :
    (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, b.val s = (orbitalGenerator(S)).val s * u s) ↔
      ∃ f : P, ∀ s : ℂ, b.val s =
        globalIdelicZFunction (adelePrincipalValue F S f.val) (ideleClassNormTwist χ s) := by
  let L := fun s : ℂ ↦ (orbitalGenerator(S)).val s
  let ev := fun b : B ↦ b.val
  let val (f : P) (s : ℂ) :=
    globalIdelicZFunction (adelePrincipalValue F S f.val) (ideleClassNormTwist χ s)
  have hev : Injective ev := Subtype.val_injective
  change (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, b.val s = L s * u s) ↔ ∃ f, ∀ s, ev b s = val f s
  let K := (homogeneousAdelicThetaLinearMap F (ω(χ))).ker
  let A := K.mkQ.comp (adelePrincipalValue F S)
  let q : P → A.range := fun f ↦ A.rangeRestrict f.val
  obtain ⟨M, _, hM, hRange⟩ := globalPrincipalValueConverse_nontrivial S χ hω
  have hq : Surjective q := (globalPrincipalValueConverse_nontrivial_exact S (ω(χ)) hω).surjective
  have hL : L = fun s ↦ reciprocalPartialHeckeEulerProduct χ S s *
      continuedCompletedHeckeL χ s := by
    funext s
    change reciprocalPartialHeckeEulerProduct χ S s *
      (regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
        (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2).val s = _
    rw [congrFun (specDenom_L0 χ τ hτ (specDenom_hδ χ hω)) s]
  rw [hL]
  have heq (f : P) (s : ℂ) : (M (q f)).val s =
      globalIdelicZFunction (adelePrincipalValue F S f.val) (ideleClassNormTwist χ s) :=
    hM f.val s
  with_reducible exact finiteNuclearity_values_of_range q hq M ev _ hRange hev val heq b

open Classical in
/-- The polar principal-value image has precisely the Mellin transforms
divisible by the regularized completed function with the Euler factors removed. -/
private theorem finiteNuclearity_mellin_values (p : HeightOneSpectrum (𝓞 ℚ)) (b : B) :
    b ∈ schwartzBergmanDivisible (orbitalGenerator(Sₚ(p))) ↔
      ∃ f : P, ∀ s : ℂ, b.val s =
        globalIdelicZFunction (adelePrincipalValue F (Sₚ(p)) f.val) (ideleClassNormTwist χ s) := by
  refine (specDenom_mem_div (orbitalGenerator(Sₚ(p))) b).trans ?_
  by_cases hω : ω(χ) = 1
  · exact finiteNuclearity_mellin_values_normTwist χ τ hτ (Sₚ(p)) b hω
  · exact finiteNuclearity_mellin_values_nontrivial χ τ hτ (Sₚ(p)) b hω

private theorem finiteNuclearity_mellin_mem (p : HeightOneSpectrum (𝓞 ℚ)) (x : Θ₀(χ)) :
    x ∈ finiteNuclearityDenominator χ p ↔
      (Z(χ, τ, hτ)) x ∈ schwartzBergmanDivisible (orbitalGenerator(Sₚ(p))) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective (Π(χ)) x
  rw [← Submodule.Quotient.mk_eq_zero (finiteNuclearityDenominator χ p),
    ← Submodule.mkQ_apply, finiteNuclearityQuotient_mk_eq_zero,
    finiteNuclearity_mellin_values χ τ hτ p]
  refine exists_congr fun f ↦ ?_
  let fv : P := ⟨adelePrincipalValue F (Sₚ(p)) f.val, nuclearityPrincipalValue_mem_polar p f⟩
  have hv (s : ℂ) := ((exists_globalPolarThetaMellin χ τ hτ).choose_spec fv s).2
  exact ⟨fun h s ↦ (congrArg (fun y : Θ₀(χ) ↦ ((Z(χ, τ, hτ)) y).val s) h).trans (hv s),
    fun h ↦ finiteNuclearity_mellin_injective χ τ hτ
      (specDenom_B_ext _ _ fun s ↦ (h s).trans (hv s).symm)⟩

/-- Paper: Theorem 7.4.2.1(1), p. 367.
The finite-place denominator is closed and is stable under each regularized action. -/
theorem finiteNuclearityDenominator_closed_invariant (p : HeightOneSpectrum (𝓞 ℚ)) (φ : 𝒟) :
    let D := finiteNuclearityDenominator χ p
    IsClosed (D : Set (Θ₀(χ))) ∧ Set.MapsTo (Aθ(φ)) (D : Set (Θ₀(χ))) D := by
  let G := orbitalGenerator(Sₚ(p))
  constructor
  · rw [show (finiteNuclearityDenominator χ p : Set (Θ₀(χ))) =
      (Z(χ, τ, hτ)) ⁻¹' (schwartzBergmanDivisible G : Set B) from
        Set.ext (finiteNuclearity_mellin_mem χ τ hτ p)]
    exact (schwartzBergmanDivisible_isClosed G).preimage (Z(χ, τ, hτ)).continuous
  · intro x hx
    have hmem (y : Θ₀(χ)) := (finiteNuclearity_mellin_mem χ τ hτ p y).trans
      (specDenom_mem_div G ((Z(χ, τ, hτ)) y))
    obtain ⟨u, hu, hv⟩ := (hmem x).mp hx
    refine (hmem _).mpr ⟨fun s ↦ nuclearityTestMellin χ φ s * u s, ?_, fun s ↦ ?_⟩
    · exact (archNuclearityDenominator_closed_invariant_multiplier χ φ).mul hu
    · rw [(exists_polarThetaNuclearityAction χ τ hτ φ).choose_spec.1 x s, hv s]
      ring

/-- Vanishing orders characterize entire divisibility, as in §7.1,
`schwartzBergmanDivisible_isClosed_dvd`. -/
private theorem finiteNuclearity_trace_dvd (g f : Entire) :
    g ∣ f ↔ ∀ z, analyticOrderAt (g.val : ℂ → ℂ) z ≤ analyticOrderAt (f.val : ℂ → ℂ) z := by
  have ha (a : Entire) (z : ℂ) : AnalyticAt ℂ (a.val : ℂ → ℂ) z :=
    (show Differentiable ℂ a.val from a.property).analyticAt z
  constructor
  · rintro ⟨k, rfl⟩ z
    change _ ≤ analyticOrderAt ((g.val : ℂ → ℂ) * (k.val : ℂ → ℂ)) z
    rw [analyticOrderAt_mul (ha g z) (ha k z)]
    exact self_le_add_right _ _
  · intro hord
    let q := (f.val : ℂ → ℂ) / (g.val : ℂ → ℂ)
    have hq : MeromorphicOn q univ := fun z _ ↦ (ha f z).meromorphicAt.div (ha g z).meromorphicAt
    have hdiff : Differentiable ℂ (toMeromorphicNFOn q univ) := by
      intro z
      apply AnalyticAt.differentiableAt
      have hnf := meromorphicNFOn_toMeromorphicNFOn q univ (mem_univ z)
      apply hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [meromorphicOrderAt_toMeromorphicNFOn hq (mem_univ z),
        meromorphicOrderAt_div (ha f z).meromorphicAt (ha g z).meromorphicAt,
        (ha f z).meromorphicOrderAt_eq, (ha g z).meromorphicOrderAt_eq]
      have hle := hord z
      generalize analyticOrderAt (f.val : ℂ → ℂ) z = m at hle ⊢
      generalize analyticOrderAt (g.val : ℂ → ℂ) z = n at hle ⊢
      cases m using ENat.recTopCoe with
      | top => simp
      | coe m =>
        cases n using ENat.recTopCoe with
        | top => simp at hle
        | coe n =>
          exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr (by exact_mod_cast hle : (n : ℤ) ≤ m))
    refine ⟨⟨⟨_, hdiff.continuous⟩, hdiff⟩, Subtype.ext (ContinuousMap.ext fun z ↦ ?_)⟩
    change f.val z = g.val z * toMeromorphicNFOn q univ z
    by_cases hz : g.val z = 0
    · have hpos := lt_of_lt_of_le (pos_iff_ne_zero.mpr ((ha g z).analyticOrderAt_ne_zero.mpr hz))
          (hord z)
      rw [hz, zero_mul]
      exact (ha f z).analyticOrderAt_ne_zero.mp hpos.ne'
    · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hq (mem_univ z),
        toMeromorphicNFAt_eq_self.mpr ((ha f z).div (ha g z) hz).meromorphicNFAt]
      exact (mul_div_cancel₀ _ hz).symm

/-- The Schwartz–Bergman divisibility condition is detected by ordinary derivative jets. -/
private theorem finiteNuclearity_trace_divisible (g : Entire) (f : B) :
    f ∈ schwartzBergmanDivisible g ↔ ∀ z (k : ℕ), (k : ℕ∞) < analyticOrderAt (g.val : ℂ → ℂ) z →
      iteratedDeriv k f.val z = 0 := by
  change schwartzBergmanEntireInclusion f ∈ Ideal.span ({g} : Set Entire) ↔ _
  rw [Ideal.mem_span_singleton, finiteNuclearity_trace_dvd]
  have hv : ((schwartzBergmanEntireInclusion f).val : ℂ → ℂ) = f.val :=
    funext (schwartzBergmanEntireInclusion_apply f)
  rw [hv]
  apply forall_congr'
  intro z
  have hf : Differentiable ℂ f.val := fun w ↦
    (f.property.2.1 w (mem_univ w)).differentiableAt (Filter.univ_mem' mem_univ)
  have ha := hf.analyticAt z
  constructor
  · intro h k hk
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha).mp
      (((ENat.add_one_le_iff (ENat.natCast_ne_top k)).mpr hk).trans h) k (Nat.lt_succ_self k)
  · intro h
    by_contra! hlt
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hlt.ne_top
    have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha (n := k+1)).mpr
      (fun i hi ↦ h i ((show (i : ℕ∞) ≤ k by exact_mod_cast (Nat.le_of_lt_succ hi)).trans_lt
        (hk ▸ hlt)))
    rw [← hk] at hle
    exact (Nat.not_succ_le_self k) (by exact_mod_cast hle)

/-- The Euler zeros lie on the imaginary axis, where the regularized completed
generator has order zero. Thus the two sets of jet conditions are disjoint. -/
private theorem finiteNuclearity_trace_orders (p : HeightOneSpectrum (𝓞 ℚ)) :
    let R := reciprocalPartialHeckeEulerProduct χ (Sₚ(p))
    let G := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    (∀ z, ((analyticOrderAt R z).toNat : ℕ∞) = analyticOrderAt R z) ∧
    (∀ z, 0 < analyticOrderAt R z → analyticOrderAt (G.val : ℂ → ℂ) z = 0) ∧
    ∀ z, analyticOrderAt ((orbitalGenerator(Sₚ(p))).val : ℂ → ℂ) z =
      max (analyticOrderAt (G.val : ℂ → ℂ) z) (analyticOrderAt R z) := by
  classical
  intro R G
  let S := Sₚ(p)
  have hs : S.filter (fun v ↦ v.under (𝓞 ℚ) = p) = S := by
    ext v
    exact Finset.mem_filter.trans (and_iff_left_of_imp fun hv ↦
      (finite_nuclearityPlacesAbove (F := F) p).mem_toFinset.mp hv)
  have ha : Differentiable ℂ R := by
    apply Differentiable.fun_finsetProd
    intro v _
    by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v
    · simp only [finiteHeckeEulerFactor, ite_eq_left hv, inv_inv]
      have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
        exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
      exact (differentiable_const _).sub ((differentiable_const _).mul
        (differentiable_id.neg.const_cpow (.inl hq)))
    · simp only [finiteHeckeEulerFactor, ite_eq_right hv, inv_one]
      exact differentiable_const _
  constructor
  · intro z
    have h := reciprocalEulerProduct_over_prime_order_le χ S p z
    rw [hs] at h
    exact ENat.natCast_toNat ((lt_of_le_of_lt h (ENat.natCast_lt_top _)).ne)
  · have disjoint (z : ℂ) (h : 0 < analyticOrderAt R z) :
        analyticOrderAt (G.val : ℂ → ℂ) z = 0 := by
      have hl := reciprocalEulerProduct_over_prime_zero χ S p (s := z)
      rw [hs] at hl
      obtain ⟨_, _, _, _, _, _, _, he⟩ := hl ((ha.analyticAt z).analyticOrderAt_ne_zero.mp h.ne')
      have hre : z.re = 0 := by
        rw [he, Complex.mul_re, Complex.I_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
      by_contra hn
      obtain ⟨n, hn', _, hdiv⟩ := spectralNuclearity_trace_zero_order χ τ hτ
        ⟨z, pos_iff_ne_zero.mpr hn⟩
      exact (spectralNuclearity_trace_zero_strip χ (z := z)
        (by rw [hdiv]; exact_mod_cast hn')).1.ne' hre
    refine ⟨disjoint, fun z ↦ ?_⟩
    change analyticOrderAt (R * (G.val : ℂ → ℂ)) z = _
    rw [analyticOrderAt_mul (ha.analyticAt z)
      ((show Differentiable ℂ G.val from G.property).analyticAt z)]
    by_cases h : analyticOrderAt R z = 0
    · simp [h]
    · simp [disjoint z (pos_iff_ne_zero.mpr h)]

open Classical in
/-- The Mellin jets up to the full local Euler order separate the polar quotient.
The comparison vectors of §7.1 lift to polar classes because all their completed
L-function jets vanish. -/
private theorem finiteNuclearity_trace_jets (p : HeightOneSpectrum (𝓞 ℚ)) :
    let D := finiteNuclearityDenominator χ p
    let R := reciprocalPartialHeckeEulerProduct χ (Sₚ(p))
    let Zeros := {z : ℂ // 0 < analyticOrderAt R z}
    let J := Σ z : Zeros, Fin (analyticOrderAt R z.val).toNat
    ∃ (d : J → StrongDual ℂ (Θ₀(χ) ⧸ D)) (b : J → Θ₀(χ) ⧸ D),
      (∀ j x, d j (D.mkQ x) = iteratedDeriv j.2.val ((Z(χ, τ, hτ)) x).val j.1.val) ∧
      (∀ i j, d i (b j) = if i = j then 1 else 0) ∧
      ∀ x, (∀ j, d j x = 0) → x = 0 := by
  classical
  intro D R Zeros J
  let G := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
  let H := orbitalGenerator(Sₚ(p))
  let ord (g : Entire) (z : ℂ) := analyticOrderAt (g.val : ℂ → ℂ) z
  obtain ⟨hfinite, hdisjoint, hmax⟩ := finiteNuclearity_trace_orders χ τ hτ p
  have range_iff (f : B) : (∃ x, (Z(χ, τ, hτ)) x = f) ↔
      ∀ z (k : ℕ), (k : ℕ∞) < ord G z → iteratedDeriv k f.val z = 0 :=
    (specDenom_range_mem χ τ hτ f).trans
      ((specDenom_mem_div G f).symm.trans (finiteNuclearity_trace_divisible G f))
  let jet (j : J) :=
    ((entireJet j.1.val j.2.val).comp schwartzBergmanEntireInclusion).comp (Z(χ, τ, hτ))
  have eval (j : J) (x : Θ₀(χ)) :
      jet j x = iteratedDeriv j.2.val ((Z(χ, τ, hτ)) x).val j.1.val := by
    dsimp only [jet, ContinuousLinearMap.comp_apply]
    rw [entireJet_apply]
    exact congrArg (fun f : ℂ → ℂ ↦ iteratedDeriv j.2.val f j.1.val)
      (funext (schwartzBergmanEntireInclusion_apply _))
  have jk (j : J) : (j.2.val : ℕ∞) < analyticOrderAt R j.1.val := by
    apply lt_of_lt_of_eq ?_ (hfinite j.1.val)
    exact_mod_cast j.2.isLt
  have den (x : Θ₀(χ)) : x ∈ D ↔ ∀ j, jet j x = 0 := by
    rw [finiteNuclearity_mellin_mem χ τ hτ p, finiteNuclearity_trace_divisible]
    constructor
    · intro h j
      rw [eval]
      exact h _ _ ((jk j).trans_le ((le_max_right _ _).trans_eq (hmax _).symm))
    · intro h z k hk
      rw [hmax, lt_max_iff] at hk
      rcases hk with hk | hk
      · exact (range_iff _).mp ⟨x, rfl⟩ z k hk
      · let z' : Zeros := ⟨z, zero_le.trans_lt hk⟩
        have hk' : k < (analyticOrderAt R z).toNat := by
          rw [← hfinite] at hk
          exact_mod_cast hk
        exact (eval ⟨z', k, hk'⟩ x).symm.trans (h ⟨z', k, hk'⟩)
  let d (j : J) := D.liftQL (jet j) (fun x hx ↦ (den x).mp hx j)
  let I := {i : ℂ × ℕ // (i.2 : ℕ∞) < ord H i.1}
  let i (j : J) : I := ⟨(j.1.val, j.2.val), (jk j).trans_le
    ((le_max_right _ _).trans_eq (hmax _).symm)⟩
  have inj : Injective i := by
    rintro ⟨z, k⟩ ⟨w, l⟩ he
    have ez : z = w := Subtype.ext (congrArg (fun v : I ↦ v.val.1) he)
    subst w
    exact congrArg (Sigma.mk z) (Fin.ext (congrArg (fun v : I ↦ v.val.2) he))
  obtain ⟨v, hv⟩ := orbitalSchwartzBergman_biorthogonal χ τ hτ (continuedCompletedHeckeL χ)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2 (Sₚ(p))
  have lift (j : J) : ∃ x, (Z(χ, τ, hτ)) x = v (i j) := by
    apply (range_iff _).mpr
    intro z k hk
    let l : I := ⟨(z, k), hk.trans_le ((le_max_left _ _).trans_eq (hmax z).symm)⟩
    have hne : l ≠ i j := by
      intro he
      have hz : z = j.1.val := congrArg (fun t : I ↦ t.val.1) he
      exact (not_lt_of_ge (zero_le : (0 : ℕ∞) ≤ k))
        (hk.trans_eq (hz ▸ hdisjoint _ j.1.property))
    exact (hv l (i j)).trans (ite_eq_right hne)
  choose u hu using lift
  refine ⟨d, fun j ↦ D.mkQ (u j), eval, fun a j ↦ ?_, ?_⟩
  · change jet a (u j) = _
    rw [eval, hu]
    exact (hv (i a) (i j)).trans (by simp only [inj.eq_iff])
  · intro x hx
    obtain ⟨y, rfl⟩ := D.mkQ_surjective x
    exact (Submodule.Quotient.mk_eq_zero D).mpr ((den y).mpr hx)

/-- A closed quotient of a space embedded linearly in a nuclear space is nuclear. -/
private theorem finiteNuclearity_trace_quotient_nuclear {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (f : X →L[ℂ] Y) (hf : IsEmbedding f) (hY : IsNuclearTVS.{0} Y)
    (D : Submodule ℂ X) (hD : IsClosed (D : Set X)) : IsNuclearTVS.{0} (X ⧸ D) := by
  let := hY.2.1
  let : PolynormableSpace ℂ X := hf.isInducing.polynormableSpace (f := f.toLinearMap)
  let e := LinearEquiv.ofInjective f.toLinearMap hf.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hf.isInducing
  let h := e.toEquiv.toHomeomorphOfIsInducing he
  let L : X ≃L[ℂ] f.range := ⟨e, h.continuous, h.continuous_symm⟩
  exact isNuclearTVS_quotient (nuclear_of_equiv L.symm (isNuclearTVS_submodule hY f.range)) D

open Classical in
/-- In a multiplication action on jets, the Leibniz terms with a positive-order
derivative of the multiplier vanish on the matching biorthogonal vector. -/
private theorem finiteNuclearity_trace_diagonal {X E Z : Type*} [DecidableEq Z] [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (p : X → E) (hp : Surjective p) (A : X → X) (T : E → E)
    (hT : ∀ x, T (p x) = p (A x)) (f : X → ℂ → ℂ) (hf : ∀ x, Differentiable ℂ (f x))
    (M : ℂ → ℂ) (hM : Differentiable ℂ M) (hA : ∀ x, f (A x) = M * f x)
    (z : Z → ℂ) (m : Z → ℕ)
    (d : (Σ s, Fin (m s)) → StrongDual ℂ E) (b : (Σ s, Fin (m s)) → E)
    (hd : ∀ j x, d j (p x) = iteratedDeriv j.2.val (f x) (z j.1))
    (hb : ∀ i j, d i (b j) = if i = j then 1 else 0) (j : Σ s, Fin (m s)) :
    d j (T (b j)) = M (z j.1) := by
  obtain ⟨x, hx⟩ := hp (b j)
  rw [← hx, hT, hd, hA, iteratedDeriv_mul hM.contDiff.contDiffAt (hf x).contDiff.contDiffAt,
    Finset.sum_eq_single 0]
  · simp [← hd j x, hx, hb]
  · intro k hk hk0
    let i : Σ s, Fin (m s) := ⟨j.1, j.2.val - k, (Nat.sub_le _ _).trans_lt j.2.isLt⟩
    have hij : i ≠ j := by
      intro he
      have h := congrArg (fun u : Σ s, Fin (m s) ↦ u.2.val) he
      have hk' := Finset.mem_range.mp hk
      change j.2.val - k = j.2.val at h
      omega
    rw [← hd i x, hx, hb, ite_eq_right hij, mul_zero]
  · simp

open Classical in
/-- Synthesize the rank-one series in the complete disc, then use the separating
jets to identify its sum with the action. The approximation property identifies
the traces of all presentations. Each finite fiber contributes its multiplicity. -/
private theorem finiteNuclearity_trace_of_bounds {E Z : Type*} [DecidableEq Z] [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E]
    (T : E →L[ℂ] E) (hE : IsNuclearTVS.{0} E) (m : Z → ℕ) (M : Z → ℂ)
    (d : (Σ z, Fin (m z)) → StrongDual ℂ E) (b : (Σ z, Fin (m z)) → E)
    (hb : ∀ i j, d i (b j) = if i = j then 1 else 0) (hsep : ∀ x, (∀ j, d j x = 0) → x = 0)
    (hdiag : ∀ j, d j (T (b j)) = M j.1)
    (e : (Σ z, Fin (m z)) ↪ ℕ) (a c : (Σ z, Fin (m z)) → ℂˣ) (B₀ : Set E) (q : Seminorm ℂ E)
    (hB : IsBanachDisc B₀) (hv : ∀ j, (a j : ℂ) • b j ∈ B₀) (hq : Continuous q)
    (hd : ∀ j x, ‖((c j : ℂ) * (a j : ℂ))⁻¹ * d j (T x)‖ ≤ q x)
    (hr : ∀ k : ℕ, ∃ C : ℝ, ∀ j, ‖(c j : ℂ)‖ * ((e j : ℝ) + 1) ^ k ≤ C) :
    IsStronglyNuclearOperator T ∧ Summable (fun z ↦ ‖(m z : ℂ) * M z‖) ∧
    ∀ r : NuclearPresentation T, HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val)
      (∑' z, (m z : ℂ) * M z) := by
  classical
  let := hE.1
  let := hE.2.1
  let J := Σ z, Fin (m z)
  let G := WithLocalSeminorm (gaugeSeminorm hB.balanced hB.convex hB.absorbent)
  let : CompleteSpace G := hB.complete
  let : T2Space G := hB.separated
  let v (j : J) : G := ⟨(a j : ℂ) • b j, Submodule.subset_span (hv j)⟩
  let L (j : J) : StrongDual ℂ E := ((c j : ℂ) * (a j : ℂ))⁻¹ • (d j).comp T
  let u := extend e v (fun _ ↦ (0 : G))
  let ℓ := extend e L (fun _ ↦ (0 : StrongDual ℂ E))
  let coeff := extend e (fun j ↦ (c j : ℂ)) (fun _ ↦ 0)
  let incl : G →L[ℂ] E := ⟨(Submodule.span ℂ B₀).subtype, spectralTrace_banachDisc_inclusion hB⟩
  have mem (n) : incl (u n) ∈ B₀ := by
    by_cases h : n ∈ range e
    · obtain ⟨j, rfl⟩ := h
      rw [show u (e j) = v j from e.injective.extend_apply _ _ _]
      exact hv j
    · simpa only [u, extend_apply' _ _ _ h, map_zero] using
        (show (0 : E) ∈ B₀ from hB.absorbent.zero_mem)
  have rapid (k : ℕ) : ∃ C : ℝ, ∀ n, ‖coeff n‖ * ((n : ℝ) + 1) ^ k ≤ C := by
    obtain ⟨C, hC⟩ := hr k
    refine ⟨max C 0, fun n ↦ ?_⟩
    by_cases h : n ∈ range e
    · obtain ⟨j, rfl⟩ := h
      simpa only [coeff, e.injective.extend_apply] using (hC j).trans (le_max_left C 0)
    · simp [coeff, extend_apply' _ _ _ h]
  have hsum : Summable (fun n ↦ ‖coeff n‖) := by
    obtain ⟨C, hC⟩ := rapid 2
    have h : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2) := by
      simpa only [Real.rpow_two, sq_abs] using (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      exact hC n) (h.mul_left C)
  have bound (n x) : ‖ℓ n x‖ ≤ q x := by
    by_cases h : n ∈ range e
    · obtain ⟨j, rfl⟩ := h
      rw [show ℓ (e j) = L j from e.injective.extend_apply _ _ _]
      exact hd j x
    · simp [ℓ, extend_apply' _ _ _ h, apply_nonneg]
  have hequi : EquicontinuousAt (fun n x ↦ ℓ n x) 0 := by
    apply Metric.equicontinuousAt_of_continuity_modulus (fun x ↦ q x)
      (by simpa using hq.tendsto 0)
    exact Filter.Eventually.of_forall fun x n ↦ by simpa [map_zero, dist_zero_left] using bound n x
  obtain ⟨S, hS⟩ := spectralTrace_boundedSeries_toBanach ℓ u coeff hsum q hq bound
    (fun n ↦ gauge_le_one_of_mem (show u n ∈ ((↑) ⁻¹' B₀ : Set (Submodule.span ℂ B₀)) from mem n))
  have active (j : J) (x : E) :
      (coeff (e j) * ℓ (e j) x) • incl (u (e j)) = d j (T x) • b j := by
    simp only [coeff, ℓ, u, e.injective.extend_apply, L, smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
    change _ • ((a j : ℂ) • b j) = _
    rw [smul_smul]
    congr 1
    field_simp
  have series (x) : HasSum (fun n ↦ (coeff n * ℓ n x) • incl (u n)) (incl (S x)) := by
    simpa only [map_smul] using (hS x).mapL incl
  have eqT (x) : incl (S x) = T x := by
    apply sub_eq_zero.mp
    apply hsep
    intro j
    rw [map_sub, sub_eq_zero]
    have hj := (series x).mapL (d j)
    apply hj.unique
    convert hasSum_single (e j) (f := fun n ↦ d j ((coeff n * ℓ n x) • incl (u n))) ?_ using 1
    · simp [active, hb]
    · intro n hne
      by_cases h : n ∈ range e
      · obtain ⟨i, rfl⟩ := h
        have hij : j ≠ i := fun h ↦ hne (congrArg e h.symm)
        simp [active, hb, hij]
      · simp [coeff, extend_apply' _ _ _ h]
  let r : NuclearPresentation T := {
    coeff := coeff, functional := ℓ, disc := B₀, isBanachDisc := hB
    vector := fun n ↦ ⟨incl (u n), Submodule.subset_span (mem n)⟩
    vector_mem := mem, summable_coeff := hsum, equicontinuous := hequi
    hasSum := fun x ↦ eqT x ▸ series x }
  obtain ⟨t, ht, _⟩ := exists_nuclearTrace_hasSum (dense_finiteRank_of_isNuclearTVS E hE) T
    ((isNuclearOperator_iff_nonempty_presentation T).mpr ⟨r⟩)
  let scalar (n : ℕ) := coeff n * ℓ n (incl (u n))
  have hs := (e.injective.hasSum_iff (f := scalar)
    (fun n hn ↦ by simp [scalar, coeff, extend_apply' _ _ _ hn])).mpr (ht r).2
  have hjet : HasSum (fun j : Σ z, Fin (m z) ↦ M j.1) t := by
    apply hs.congr_fun
    intro j
    rw [← hdiag j]
    change d j (T (b j)) = coeff (e j) * ℓ (e j) (incl (u (e j)))
    simp only [coeff, ℓ, u, e.injective.extend_apply, L, smul_apply,
      smul_eq_mul, ContinuousLinearMap.comp_apply]
    change _ = _ * (_ * d j (T ((a j : ℂ) • b j)))
    rw [map_smul, map_smul, smul_eq_mul]
    field_simp
  have hterm : HasSum (fun z ↦ (m z : ℂ) * M z) t := hjet.sigma fun z ↦ by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using hasSum_fintype (fun _ : Fin (m z) ↦ M z)
  exact ⟨⟨r, rapid⟩, hterm.summable.norm, fun s ↦ hterm.tsum_eq.symm ▸ (ht s).2⟩

/-- Restricting the Mellin closed embedding to its range and then taking the
closed principal-value quotient preserves the Fréchet property. -/
private theorem finiteNuclearity_trace_jet_bounds_frechet {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (i : X →L[ℂ] Y) (hi : IsClosedEmbedding i) (hY : IsFrechetTVS Y)
    (D : Submodule ℂ X) (hD : IsClosed (D : Set X)) : IsFrechetTVS (X ⧸ D) := by
  obtain ⟨_, _, _, c⟩ := hY
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace Y := c
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have hu := AddMonoidHom.isUniformInducing_of_isInducing
    (f := i.toLinearMap.toAddMonoidHom) hi.isInducing
  exact isFrechetTVS_quotient
    ⟨inferInstance, hi.isInducing.polynormableSpace (f := i.toLinearMap),
      hi.isEmbedding.metrizableSpace, hu.completeSpace hi.isClosed_range.isComplete⟩ D hD

/-- A positive envelope for the test multiplier on the unit circles about the
imaginary axis. Its square dominates the multiplier and the envelope itself
still decreases faster than every inverse power of the height. -/
private theorem finiteNuclearity_trace_jet_bounds_envelope (M : ℂ → ℂ) (hM : Continuous M)
    (hdecay : ∀ k : ℕ, ∃ C : ℝ, ∀ w : ℂ, w.re ∈ Icc (-1 : ℝ) 1 →
      ‖M w‖ * (1 + |w.im|) ^ k ≤ C) :
    ∃ r : ℂ → ℝ, (∀ z, 0 < r z) ∧
      (∀ z, ∀ w ∈ Metric.sphere z 1, ‖M w‖ ≤ (r z) ^ 2) ∧
      ∀ k : ℕ, ∃ C : ℝ, ∀ z : ℂ, z.re = 0 → r z * (1 + |z.im|) ^ k ≤ C := by
  classical
  choose u hu hmax using fun z : ℂ ↦
    (isCompact_closedBall z 1).exists_isMaxOn (Metric.nonempty_closedBall.mpr zero_le_one)
      hM.norm.continuousOn
  let W (z : ℂ) := 1 + |z.im|
  let r (z : ℂ) := Real.sqrt (‖M (u z)‖ + (Real.exp (W z))⁻¹)
  have hW (z : ℂ) : 0 ≤ W z := by dsimp [W]; positivity
  have hr (z : ℂ) : 0 < r z := Real.sqrt_pos.2 (by positivity)
  have hs (z : ℂ) : (r z) ^ 2 = ‖M (u z)‖ + (Real.exp (W z))⁻¹ := Real.sq_sqrt (by positivity)
  refine ⟨r, hr, fun z w hw ↦ (hmax z (Metric.sphere_subset_closedBall hw)).trans
    ((le_add_of_nonneg_right (by positivity)).trans_eq (hs z).symm), ?_⟩
  intro k
  let n := k + k
  obtain ⟨C, hC⟩ := hdecay n
  refine ⟨Real.sqrt (C * 2 ^ n + n.factorial), fun z hz ↦ ?_⟩
  have hd := mem_closedBall_iff_norm.mp (hu z)
  have hx := (Complex.abs_re_le_norm (u z - z)).trans hd
  have hy := (Complex.abs_im_le_norm (u z - z)).trans hd
  rw [Complex.sub_re, hz, sub_zero] at hx
  rw [Complex.sub_im, abs_sub_comm] at hy
  have hw : W z ≤ 2 * W (u z) := by
    dsimp [W]
    linarith [abs_sub_abs_le_abs_sub z.im (u z).im, abs_nonneg (u z).im]
  have h₁ : ‖M (u z)‖ * W z ^ n ≤ C * 2 ^ n := calc
    _ ≤ ‖M (u z)‖ * (2 * W (u z)) ^ n := by gcongr
    _ = (‖M (u z)‖ * W (u z) ^ n) * 2 ^ n := by rw [mul_pow]; ring
    _ ≤ C * 2 ^ n := by gcongr; exact hC _ (abs_le.mp hx)
  have h₂ : (Real.exp (W z))⁻¹ * W z ^ n ≤ n.factorial := by
    rw [inv_mul_le_iff₀ (Real.exp_pos _)]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).mp
      (Real.pow_div_factorial_le_exp (W z) (hW z) n)
  apply Real.le_sqrt_of_sq_le
  calc
    (r z * W z ^ k) ^ 2 = (r z) ^ 2 * W z ^ n := by rw [mul_pow, sq (W z ^ k), ← pow_add]
    _ ≤ C * 2 ^ n + n.factorial := by rw [hs, add_mul]; exact add_le_add h₁ h₂

/-- A bounded-order Cauchy estimate with one bound on the entire input strip.
The square of the envelope accounts for the multiplier on each integration circle. -/
private theorem finiteNuclearity_trace_jet_bounds_cauchy (M : ℂ → ℂ) (hM : Differentiable ℂ M)
    (r : ℂ → ℝ)
    (hs : ∀ z, ∀ w ∈ Metric.sphere z 1, ‖M w‖ ≤ r z ^ 2)
    (N : ℕ) (f : SchwartzBergman (univ : Set ℝ)) :
    ∃ C : ℝ, ∀ (z : ℂ) (k : ℕ), z.re = 0 → k ≤ N →
      ‖iteratedDeriv k (M * f.val) z‖ ≤ r z ^ 2 * C := by
  obtain ⟨K, hK⟩ := f.property.2.2 (-1) 1 (by norm_num) (subset_univ _) 0
  have hf : Differentiable ℂ f.val := differentiableOn_univ.mp (by simpa using f.property.2.1)
  refine ⟨N.factorial * max K 0, fun z k hz hk ↦ ?_⟩
  have hcircle (w : ℂ) (hw : w ∈ Metric.sphere z 1) : ‖(M * f.val) w‖ ≤ r z ^ 2 * max K 0 := by
    have hx := (Complex.abs_re_le_norm (w - z)).trans (mem_sphere_iff_norm.mp hw).le
    rw [Complex.sub_re, hz, sub_zero] at hx
    have hb : ‖f.val w‖ ≤ K := by simpa only [pow_zero, one_mul] using hK ⟨w, abs_le.mp hx, rfl⟩
    exact (norm_mul ..).le.trans (mul_le_mul (hs z w hw) (hb.trans (le_max_left ..))
      (norm_nonneg _) (sq_nonneg _))
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k one_pos
    (hM.mul hf).diffContOnCl hcircle
  rw [one_pow, div_one] at h
  calc
    _ ≤ (k.factorial : ℝ) * (r z ^ 2 * max K 0) := h
    _ ≤ (N.factorial : ℝ) * (r z ^ 2 * max K 0) := by
      gcongr
    _ = _ := by ring

/-- Encode a jet by one vanishing local factor, its integer phase and its derivative
order. There are finitely many factor/order labels, so the code grows at most
linearly in the absolute imaginary part, even when local factors share zeros. -/
private theorem finiteNuclearity_trace_jet_bounds_enumeration
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (p : HeightOneSpectrum (𝓞 ℚ)) :
    let S := Sₚ(p)
    let R := reciprocalPartialHeckeEulerProduct χ S
    let J := Σ z : {z : ℂ // 0 < analyticOrderAt R z}, Fin (analyticOrderAt R z.val).toNat
    ∃ (e : J ↪ ℕ) (C : ℝ), ∀ j, j.1.val.re = 0 ∧ j.2.val ≤ Module.finrank ℚ F ∧
      (e j : ℝ) + 1 ≤ C * (1 + |j.1.val.im|) := by
  classical
  intro S R J
  let Z := {z : ℂ // 0 < analyticOrderAt R z}
  let l (v : S) := Real.log (v.val.asIdeal.absNorm : ℝ)
  let c (v : S) := (ideleClassNormTwist χ 0).localValue v.val
  have hl (v : S) : 0 < l v := Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val)
  have hs : S.filter (fun v ↦ v.under (𝓞 ℚ) = p) = S := by
    ext v
    exact Finset.mem_filter.trans (and_iff_left_of_imp fun hv ↦
      (finite_nuclearityPlacesAbove (F := F) p).mem_toFinset.mp hv)
  let N := Module.finrank ℚ F
  have order (z : Z) : (analyticOrderAt R z.val).toNat ≤ N := by
    have h := reciprocalEulerProduct_over_prime_order_le χ S p z.val
    rw [hs] at h
    exact ENat.toNat_le_of_le_natCast h
  have phase (z : Z) : ∃ (v : S) (n : ℤ),
      Complex.log (c v) - (l v : ℂ) * z.val = n * (2 * Real.pi * Complex.I) := by
    obtain ⟨v, hv, h⟩ := Finset.prod_eq_zero_iff.mp
      (show R z.val = 0 from apply_eq_zero_of_analyticOrderAt_ne_zero z.property.ne')
    by_cases hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v
    · let w : S := ⟨v, hv⟩
      have hc := norm_ideleClassNormTwist_zero_localValue χ v
      have hne : c w ≠ 0 := norm_ne_zero_iff.mp (hc.trans_ne one_ne_zero)
      have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
        (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
      rw [finiteHeckeEulerFactor, ite_eq_left hu, inv_inv, sub_eq_zero,
        Complex.cpow_def_of_ne_zero hq, ← Complex.natCast_log] at h
      refine ⟨w, Complex.exp_eq_one_iff.mp ?_⟩
      rw [sub_eq_add_neg, Complex.exp_add, Complex.exp_log hne]
      simpa only [l, c, w, mul_neg] using h.symm
    · simp [finiteHeckeEulerFactor, hu] at h
  choose v n hn using phase
  have hre (z : Z) : z.val.re = 0 := by
    have h := reciprocalEulerProduct_over_prime_zero χ S p (s := z.val)
    rw [hs] at h
    obtain ⟨_, _, _, _, _, _, _, he⟩ := h (apply_eq_zero_of_analyticOrderAt_ne_zero z.property.ne')
    rw [he, Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero]
  let label (j : J) : S × Fin (N + 1) := ⟨v j.1, j.2.val, by
    exact Nat.lt_succ_of_le (j.2.isLt.le.trans (order _))⟩
  let code := Fintype.equivFin (S × Fin (N + 1))
  let L := Fintype.card (S × Fin (N + 1)) + 1
  let tag (j : J) : Fin L := (code (label j)).castSucc
  let e (j : J) := (Nat.divModEquiv L).symm (Equiv.intEquivNat (n j.1), tag j)
  have inj : Injective e := by
    intro i j h
    have he := (Nat.divModEquiv L).symm.injective h
    have hi := Equiv.intEquivNat.injective (congrArg Prod.fst he)
    have ht := code.injective (Fin.castSucc_injective _ (congrArg Prod.snd he))
    have hv : v i.1 = v j.1 := congrArg Prod.fst ht
    have hp := hn i.1
    rw [hv, hi, ← hn j.1] at hp
    have hz : i.1 = j.1 := Subtype.ext (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (hl _).ne')
      (sub_right_injective hp))
    have hk : i.2.val = j.2.val := congrArg (fun a : S × Fin (N + 1) ↦ a.2.val) ht
    cases i with | mk z k =>
      cases j with | mk w m =>
        cases hz
        exact congrArg (Sigma.mk z) (Fin.ext hk)
  let K := 1 + ∑ w : S, l w
  have hK (w : S) : l w ≤ K := (Finset.single_le_sum
    (f := l) (fun u _ ↦ (hl u).le) (Finset.mem_univ w)).trans (by dsimp [K]; linarith)
  let A := (Real.pi + K) / (2 * Real.pi)
  have hA (z : Z) : |((n z : ℤ) : ℝ)| ≤ A * (1 + |z.val.im|) := by
    have hi := congrArg Complex.im (hn z)
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, Complex.intCast_re, Complex.intCast_im, Complex.log_im,
      Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, sub_zero,
      zero_mul, mul_zero, mul_one, add_zero] at hi
    have hb := abs_sub ((c (v z)).arg) (l (v z) * z.val.im)
    rw [hi, abs_mul, abs_of_pos Real.two_pi_pos, abs_mul, abs_of_pos (hl _)] at hb
    dsimp only [A]
    rw [div_mul_eq_mul_div, le_div_iff₀ Real.two_pi_pos]
    have h₁ := Complex.abs_arg_le_pi (c (v z))
    have h₂ := mul_le_mul_of_nonneg_right (hK (v z)) (abs_nonneg z.val.im)
    have hk₀ := (hl (v z)).le.trans (hK (v z))
    nlinarith [mul_nonneg Real.pi_pos.le (abs_nonneg z.val.im)]
  refine ⟨⟨e, inj⟩, (L : ℝ) * (2 * (1 + A)), fun j ↦ ⟨hre _, j.2.isLt.le.trans (order _), ?_⟩⟩
  let m := Equiv.intEquivNat (n j.1)
  have hm := (latticeWeight_bounds m).2.2
  simp only [m, latticeWeight, Equiv.symm_apply_apply] at hm
  have hb : (m : ℝ) + 1 ≤ (2 * (1 + A)) * (1 + |j.1.val.im|) := by
    nlinarith [hA j.1, abs_nonneg j.1.val.im]
  change ((m * L + (tag j).val : ℕ) : ℝ) + 1 ≤ _
  push_cast
  have ht : ((tag j).val : ℝ) + 1 ≤ L := by exact_mod_cast (tag j).isLt
  calc
    _ ≤ (L : ℝ) * ((m : ℝ) + 1) := by linarith only [ht]
    _ ≤ (L : ℝ) * ((2 * (1 + A)) * (1 + |j.1.val.im|)) := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ = _ := by ring

/-- In a Fréchet space a rapid positive scale absorbs polynomial column growth.
Pointwise boundedness of the rows divided by its square gives one continuous
seminorm by the barrelled-space uniform boundedness principle. -/
private theorem finiteNuclearity_trace_jet_bounds_rescale {I E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] (hE : IsFrechetTVS E)
    (e : I ↪ ℕ) (W r : I → ℝ) (hW : ∀ j, 0 ≤ W j) (hr : ∀ j, 0 < r j)
    (K : ℝ) (he : ∀ j, (e j : ℝ) + 1 ≤ K * W j)
    (hrapid : ∀ k : ℕ, ∃ C : ℝ, ∀ j, r j * W j ^ k ≤ C)
    (b : I → E) (row : I → StrongDual ℂ E)
    (hb : ∀ q : Seminorm ℂ E, Continuous q → ∃ (m : ℕ) (C : ℝ), ∀ j, q (b j) ≤ C * W j ^ m)
    (hd : ∀ x, ∃ C : ℝ, ∀ j, ‖row j x‖ ≤ r j ^ 2 * C) :
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    ∃ (a : I → ℂˣ) (disc : Set E) (q : Seminorm ℂ E),
      IsBanachDisc disc ∧ (∀ j, (a j : ℂ) • b j ∈ disc) ∧ Continuous q ∧
      (∀ j x, ‖((a j : ℂ) * (a j : ℂ))⁻¹ * row j x‖ ≤ q x) ∧
      ∀ k : ℕ, ∃ C : ℝ, ∀ j, ‖(a j : ℂ)‖ * ((e j : ℝ) + 1) ^ k ≤ C := by
  classical
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : BarrelledSpace ℂ E := isFrechetTVS_barrelled hE
  obtain ⟨_, hpoly, hmet, hcomp⟩ := hE
  let : CompleteSpace E := hcomp
  let a (j : I) : ℂˣ := Units.mk0 (r j : ℂ) (Complex.ofReal_ne_zero.mpr (hr j).ne')
  have ha (j : I) : ‖(a j : ℂ)‖ = r j := Complex.norm_of_nonneg (hr j).le
  have hbounded : Bornology.IsVonNBounded ℂ (range fun j ↦ (a j : ℂ) • b j) := by
    apply (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bddAbove.mpr
    intro q
    obtain ⟨m, C, hC⟩ := hb q.val q.property
    obtain ⟨L, hL⟩ := hrapid m
    refine ⟨max C 0 * L, ?_⟩
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    change q.val ((a j : ℂ) • b j) ≤ _
    rw [map_smul_eq_mul, ha]
    calc
      _ ≤ r j * (max C 0 * W j ^ m) := by
        apply mul_le_mul_of_nonneg_left _ (hr j).le
        exact (hC j).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg (hW _) _))
      _ = max C 0 * (r j * W j ^ m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hL j) (le_max_right ..)
  obtain ⟨disc, hdisc, hv⟩ := exists_isBanachDisc_of_isVonNBounded_range _ hbounded
  let scaled (j : I) : StrongDual ℂ E := ((a j : ℂ) * (a j : ℂ))⁻¹ • row j
  let norms (j : I) := (normSeminorm ℂ ℂ).comp (scaled j).toLinearMap
  have bounded : BddAbove (range norms) := by
    rw [Seminorm.bddAbove_range_iff]
    intro x
    obtain ⟨C, hC⟩ := hd x
    refine ⟨C, forall_mem_range.mpr fun j ↦ ?_⟩
    change ‖((a j : ℂ) * (a j : ℂ))⁻¹ * row j x‖ ≤ C
    rw [norm_mul, norm_inv, norm_mul, ha, ← sq, inv_mul_le_iff₀ (sq_pos_of_pos (hr j))]
    exact hC j
  have hq : Continuous ⇑(⨆ j, norms j) := by
    rw [Seminorm.coe_iSup_eq bounded]
    exact Seminorm.continuous_iSup norms (fun j ↦ (scaled j).continuous.norm) bounded
  refine ⟨a, disc, ⨆ j, norms j, hdisc, hv, hq, fun j x ↦ (le_ciSup bounded j : norms j ≤ _) x, ?_⟩
  intro k
  obtain ⟨C, hC⟩ := hrapid k
  refine ⟨(max K 0) ^ k * C, fun j ↦ ?_⟩
  rw [ha]
  have h := (he j).trans (mul_le_mul_of_nonneg_right (le_max_left K 0) (hW j))
  calc
    _ ≤ r j * (max K 0 * W j) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h k) (hr j).le
    _ = (max K 0) ^ k * (r j * W j ^ k) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hC j) (by positivity)

/-- One extra power of strip decay dominates the weighted vertical trace by an
L² function independent of the jet. A continuous seminorm uses finitely many such traces. -/
private theorem finiteNuclearity_trace_jet_bounds_cardinal_growth_seminorm {J : Type*}
    (w : J → ℝ) (hw : ∀ j, 1 ≤ w j) (f : J → B)
    (hb : ∀ A : ℝ, ∀ n : ℕ, ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ j (z : ℂ), |z.re| ≤ A →
      (1 + ‖z‖) ^ n * ‖(f j).val z‖ ≤ C * w j ^ m)
    (q : Seminorm ℂ B) (hq : Continuous q) :
    ∃ (m : ℕ) (C : ℝ), ∀ j, q (f j) ≤ C * w j ^ m := by
  classical
  let I := (univ : Set ℝ)
  let lineNorm (i : I × ℕ) : Seminorm ℂ B := Seminorm.of
    (fun g : schwartzBergmanSubmodule I ↦ (eLpNorm (weightedVerticalTrace i.1 i.2 g.val) 2 volume).toReal)
    (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  have hP : WithSeminorms lineNorm := withGeneratingSeminorms_spec (schwartzBergmanSubmodule I) lineNorm
  let u (t : ℝ) := (1 + ‖t‖)⁻¹
  have hu : MemLp u 2 volume := by
    apply (integrable_norm_rpow_iff (by dsimp [u]; fun_prop) (by norm_num) (by norm_num)).mp
    have hnorm (t : ℝ) : ‖u t‖ = (1 + ‖t‖)⁻¹ := Real.norm_of_nonneg (by dsimp [u]; positivity)
    simpa only [hnorm, Real.rpow_neg_eq_inv_rpow] using
      (integrable_one_add_norm (μ := (volume : Measure ℝ)) (r := (2 : ENNReal).toReal) (by simp))
  have line (i : I × ℕ) : ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ j, lineNorm i (f j) ≤ C * w j ^ m := by
    obtain ⟨m, C, hC, h⟩ := hb |(i.1 : ℝ)| (i.2 + 1)
    refine ⟨m, C * lpNorm u 2 volume, mul_nonneg hC (lpNorm_nonneg ..), fun j ↦ ?_⟩
    let K := C * w j ^ m
    have hK : 0 ≤ K := mul_nonneg hC (pow_nonneg (zero_le_one.trans (hw j)) _)
    have bound (t : ℝ) : ‖weightedVerticalTrace i.1 i.2 (f j).val t‖ ≤ (K • u) t := by
      let z : ℂ := (i.1 : ℝ) + t * Complex.I
      have ht : ‖t‖ ≤ ‖z‖ := by simpa [z, Real.norm_eq_abs] using Complex.abs_im_le_norm z
      change ‖z ^ i.2 * (f j).val z‖ ≤ K * (1 + ‖t‖)⁻¹
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), norm_mul, norm_pow]
      calc
        _ ≤ ((1 + ‖z‖) ^ i.2 * ‖(f j).val z‖) * (1 + ‖z‖) := by gcongr; linarith
        _ = (1 + ‖z‖) ^ (i.2 + 1) * ‖(f j).val z‖ := by rw [pow_succ]; ring
        _ ≤ K := h j z (by simp [z])
    change lpNorm _ 2 volume ≤ _
    refine (lpNorm_mono_real (hu.const_smul K) bound).trans_eq ?_
    rw [lpNorm_const_smul]
    change ‖K‖ * _ = _
    rw [Real.norm_of_nonneg hK]
    dsimp [K]; ring
  obtain ⟨s, c, _, hc⟩ := Seminorm.bound_of_continuous hP q hq
  choose m C hC h using line
  let A := ∑ i ∈ s, C i
  refine ⟨s.sup m, c * A, fun j ↦ (hc _).trans ?_⟩
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ c.coe_nonneg
  apply Seminorm.finset_sup_apply_le (mul_nonneg (Finset.sum_nonneg fun i _ ↦ hC i)
    (pow_nonneg (zero_le_one.trans (hw j)) _))
  intro i hi
  exact (h i j).trans (mul_le_mul (Finset.single_le_sum (fun k _ ↦ hC k) hi)
    (pow_le_pow_right₀ (hw j) (Finset.le_sup hi)) (pow_nonneg (zero_le_one.trans (hw j)) _)
    (Finset.sum_nonneg fun k _ ↦ hC k))

/-- The inverse Euler product over one rational prime has common imaginary period
2π/log N(p), since each residue - field logarithm is an integral multiple of log N(p). -/
private theorem finiteNuclearity_trace_jet_bounds_cardinal_growth_period
    (χ : U) (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ T : ℝ, 0 < T ∧ Periodic (reciprocalPartialHeckeEulerProduct χ (Sₚ(p))) ((T : ℂ) * Complex.I) := by
  classical
  let T := 2 * Real.pi / Real.log (p.asIdeal.absNorm : ℝ)
  have hp : 1 < (p.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  refine ⟨T, div_pos Real.two_pi_pos (Real.log_pos hp), fun z ↦ Finset.prod_congr rfl fun v hv ↦ ?_⟩
  have he := (finite_nuclearityPlacesAbove (F := F) p).mem_toFinset.mp hv
  let : v.asIdeal.IsPrime := v.isPrime
  let : v.asIdeal.LiesOver p.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal he).symm⟩
  let d := v.asIdeal.inertiaDeg (𝓞 ℚ)
  have hlog : Real.log (v.asIdeal.absNorm : ℝ) = d * Real.log (p.asIdeal.absNorm : ℝ) := by
    rw [← Ideal.absNorm_pow_inertiaDeg p.asIdeal v.asIdeal, Nat.cast_pow, Real.log_pow]
  by_cases h : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · simp only [finiteHeckeEulerFactor, ite_eq_left h, inv_inv]
    have hv0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
    have hpow : (v.asIdeal.absNorm : ℂ) ^ ((T : ℂ) * Complex.I) = 1 := by
      rw [Complex.cpow_def_of_ne_zero hv0, ← Complex.natCast_log, hlog]
      have heq : d * Real.log (p.asIdeal.absNorm : ℝ) * T = (d : ℝ) * (2 * Real.pi) := by
        dsimp [T]; field_simp [(Real.log_pos hp).ne']
      have hc := congrArg (fun r : ℝ ↦ (r : ℂ) * Complex.I) heq
      push_cast at hc ⊢
      rw [← mul_assoc, hc]
      simpa only [mul_assoc, Int.cast_natCast] using Complex.exp_int_mul_two_pi_mul_I (d : ℤ)
    rw [neg_add, Complex.cpow_add _ _ hv0, Complex.cpow_neg _ ((T : ℂ) * Complex.I), hpow, inv_one, mul_one]
  · simp [finiteHeckeEulerFactor, h]

/-- Reflecting the pole - cleared finite generator gives an entire function vanishing to
the completed orders. On the imaginary axis its reciprocal has polynomial growth by
Theorem B.6.1.6 on the line Re(s) = 1. -/
private theorem finiteNuclearity_trace_jet_bounds_cardinal_growth_multiplier
    (χ : U) (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F)) :
    let G := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      (∀ z, analyticOrderAt (G.val : ℂ → ℂ) z ≤ analyticOrderAt H z) ∧
      (∀ A : ℝ, ∃ (n : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : ℂ, |z.re| ≤ A → ‖H z‖ ≤ C * (1 + ‖z‖) ^ n) ∧
      (∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : ℂ, z.re = 0 →
        H z ≠ 0 ∧ ‖(H z)⁻¹‖ ≤ C * (1 + |z.im|) ^ k) := by
  classical
  intro G
  let ψ := χ⁻¹
  let H (z : ℂ) := spectralFiniteG ψ τ hτ (1 - z)
  have hd : Differentiable ℂ H := (spectralFiniteG_diff ψ τ hτ).comp (differentiable_id.const_sub 1)
  refine ⟨H, hd, fun z ↦ ?_, fun A ↦ ?_, ?_⟩
  · by_cases hz : 0 < analyticOrderAt (G.val : ℂ → ℂ) z
    · obtain ⟨n, _, hn, _⟩ := spectralNuclearity_trace_zero_order χ τ hτ ⟨z, hz⟩
      have h := spectralBoundaryFinite_reflected_retained_order χ τ hτ 0 z hz
      change analyticOrderAt (G.val : ℂ → ℂ) z = (n : ℕ∞) at hn
      change ((analyticOrderAt (G.val : ℂ → ℂ) z).toNat : ℕ∞) ≤ _ at h
      rw [ENat.natCast_toNat (hn.trans_ne (ENat.natCast_ne_top n))] at h
      simpa only [Complex.ofReal_zero, add_zero, sub_zero] using h
    · exact (le_of_not_gt hz).trans zero_le
  · obtain ⟨n, C, hC, h⟩ := spectralBoundaryFinite_strip_growth ψ τ hτ (1 + A)
    refine ⟨n, C, hC.le, fun z hz ↦ (h (1 - z) ?_).trans ?_⟩
    · simpa using (abs_sub (1 : ℝ) z.re).trans (by simpa using add_le_add_left hz 1)
    · simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      gcongr
      exact Complex.abs_im_le_norm _
  · let G' := regularizedCompletedHeckeL ψ τ hτ (continuedCompletedHeckeL ψ)
      (continuedCompletedHeckeL_spec ψ).1 (continuedCompletedHeckeL_spec ψ).2
    have ne (w : ℂ) (hw : w.re = 1) : spectralFiniteG ψ τ hτ w ≠ 0 := by
      apply mul_ne_zero (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos ψ (by linarith)))
      intro he
      have ha : AnalyticAt ℂ (G'.val : ℂ → ℂ) w := G'.property.analyticAt _
      obtain ⟨k, hk, _, hord⟩ := spectralNuclearity_trace_zero_order ψ τ hτ
        ⟨w, pos_iff_ne_zero.mpr (ha.analyticOrderAt_ne_zero.mpr he)⟩
      exact (spectralNuclearity_trace_zero_strip ψ (by rw [hord]; exact_mod_cast hk)).2.ne hw
    obtain ⟨L, hL, hs⟩ := finiteHeckeL_exists_continuation ψ
    obtain ⟨ha, k, _, hb⟩ := finiteHeckeL_inv_isBigO_oneLine ψ L hL hs
    obtain ⟨C, hC, hb⟩ := Asymptotics.isBigO_iff'.mp hb
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (Filter.eventually_comap.mp (ha.and hb))
    let b := ((existsUnique_ideleNormSection_character_phase ψ τ hτ).exists.choose : ℂ) * Complex.I
    let S := |T| + ‖b‖ + 2
    let pole := spectralFiniteP ψ τ hτ
    let value (t : ℝ) := spectralFiniteG ψ τ hτ ⟨1, t⟩
    have hV : Continuous (fun t : ℝ ↦ (value t)⁻¹) :=
      ((spectralFiniteG_diff ψ τ hτ).continuous.comp
        (show Continuous (fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) by
          exact ((continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I)) :
            Continuous (fun t : ℝ ↦ 1 + (t : ℂ) * Complex.I)).congr (fun t ↦ by apply Complex.ext <;> simp))).inv₀ (fun t ↦ ne _ rfl)
    obtain ⟨B₀, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Icc (-S) S) hV.continuousOn
    refine ⟨k, max C B₀, hC.le.trans (le_max_left ..), fun z hz ↦ ⟨ne _ (by simp [hz]), ?_⟩⟩
    have heq : 1 - z = (⟨1, -z.im⟩ : ℂ) := by apply Complex.ext <;> simp [hz]
    rw [show H z = value (-z.im) from congrArg (spectralFiniteG ψ τ hτ) heq]
    by_cases ht : |z.im| ≤ S
    · exact (hB _ (abs_le.mp (abs_neg z.im ▸ ht))).trans ((le_max_right _ _).trans
        (le_mul_of_one_le_right (hC.le.trans (le_max_left ..)) (one_le_pow₀ (by linarith [abs_nonneg z.im]))))
    let w : ℂ := ⟨1, -z.im⟩
    have ht' := (hT |z.im| (by dsimp [S] at ht; linarith [le_abs_self T, norm_nonneg b])
      (-z.im) (abs_neg z.im))
    have hp : 1 ≤ ‖pole w‖ := by
      have h₁ : 1 ≤ ‖w + b‖ := by
        have := norm_sub_le (w + b) b
        rw [add_sub_cancel_right] at this
        have hw := Complex.abs_im_le_norm w
        dsimp [w] at hw
        rw [abs_neg] at hw
        dsimp [S] at ht; linarith [abs_nonneg T]
      have h₂ : 1 ≤ ‖1 - w - b‖ := by
        have hw := norm_sub_le (1 - w - b) (1 - b)
        rw [show 1 - w - b - (1 - b) = -w by ring, norm_neg] at hw
        have hh := Complex.abs_im_le_norm w
        dsimp [w] at hh
        rw [abs_neg] at hh
        dsimp [S] at ht; linarith [norm_sub_le (1 : ℂ) b, norm_one (α := ℂ), abs_nonneg T]
      change 1 ≤ ‖(w + b) ^ _ * (1 - w - b) ^ _‖
      rw [norm_mul, norm_pow, norm_pow]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h₁) (one_le_pow₀ h₂)
    have hm : MeromorphicOn (pole * L) univ := fun x hx ↦
      ((spectralFiniteP_diff ψ τ hτ).analyticAt x).meromorphicAt.mul (hL hx).meromorphicAt
    have hv : value (-z.im) = pole w * L w := by
      change spectralFiniteG ψ τ hτ w = _
      rw [spectralFiniteG_eq_finite ψ τ hτ L hL hs, toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _),
        toMeromorphicNFAt_eq_self.mpr (((spectralFiniteP_diff ψ τ hτ).analyticAt w).mul ht'.1.1).meromorphicNFAt]
      rfl
    have hb' : ‖(L w)⁻¹‖ ≤ C * |z.im| ^ k := by
      simpa only [abs_neg, Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)] using ht'.2
    rw [hv, mul_inv, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by simpa using inv_le_one_of_one_le₀ hp)).trans
      (hb'.trans (mul_le_mul (le_max_left ..) (pow_le_pow_left₀ (abs_nonneg _) (by linarith) k)
        (by positivity) (hC.le.trans (le_max_left ..))))

open Classical in
/-- Cardinal functions on one fundamental interval supply cardinal functions on all
its translates. The strip weight changes by at most a power of the translation height. -/
private theorem finiteNuclearity_trace_jet_bounds_cardinal_growth_translates
    (R : ℂ → ℂ) (T : ℝ) (hT : 0 < T) (hper : Periodic R ((T : ℂ) * Complex.I)) :
    let J := Σ z : {z : ℂ // 0 < analyticOrderAt R z}, Fin (analyticOrderAt R z.val).toNat
    ∀ (e : J ↪ ℕ) (K : ℝ), (∀ j, (e j : ℝ) + 1 ≤ K * (1 + |j.1.val.im|)) →
    ∀ f : J → B, (∀ i j, iteratedDeriv i.2.val (f j).val i.1.val = if i = j then 1 else 0) →
    ∃ u : J → ℂ → ℂ, (∀ j, Differentiable ℂ (u j)) ∧
      (∀ i j, iteratedDeriv i.2.val (u j) i.1.val = if i = j then 1 else 0) ∧
      ∀ A : ℝ, ∀ k : ℕ, ∃ C ≥ (0 : ℝ), ∀ j (z : ℂ), |z.re| ≤ A →
        (1 + ‖z‖) ^ k * ‖u j z‖ ≤ C * (1 + |j.1.val.im|) ^ k := by
  classical
  intro J e K he f hf
  let v (n : ℤ) : ℂ := n • ((T : ℂ) * Complex.I)
  have hord (n : ℤ) (z : ℂ) : analyticOrderAt R (z - v n) = analyticOrderAt R z := by
    have eq : R ∘ (fun x : ℂ ↦ x - v n) = R := funext fun _ ↦ hper.sub_zsmul_eq n
    rw [← analyticOrderAt_comp_of_deriv_ne_zero (f := R) (g := fun x : ℂ ↦ x - v n)
      (z₀ := z) (by fun_prop) (by simp), eq]
  let shift (n : ℤ) (j : J) : J :=
    ⟨⟨j.1.val - v n, (hord n _).symm ▸ j.1.property⟩, ⟨j.2.val, by rw [hord]; exact j.2.isLt⟩⟩
  have shift_inj (n : ℤ) : Injective (shift n) := by
    rintro ⟨z, k⟩ ⟨w, l⟩ h
    have hz : z = w := Subtype.ext (sub_left_injective (congrArg (fun j : J ↦ j.1.val) h))
    subst w
    exact congrArg (Sigma.mk z) (Fin.ext (congrArg (fun j : J ↦ j.2.val) h))
  let n (j : J) := ⌊j.1.val.im / T⌋
  let rep (j : J) := shift (n j) j
  have hband (j : J) : |(rep j).1.val.im| ≤ T := by
    have h₁ := (le_div_iff₀ hT).mp (Int.floor_le (j.1.val.im / T))
    have h₂ := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one (j.1.val.im / T))
    change |(j.1.val - v (n j)).im| ≤ _
    simp only [v, zsmul_eq_mul, Complex.sub_im, ← mul_assoc, ← Complex.ofReal_intCast,
      ← Complex.ofReal_mul, Complex.mul_I_im, Complex.ofReal_re]
    dsimp only [n]
    rw [abs_of_nonneg (sub_nonneg.mpr h₁)]
    linarith
  let band := {i : J // |i.1.val.im| ≤ T}
  obtain ⟨M, hM⟩ := exists_nat_gt (max K 0 * (1 + T))
  have heM (i : band) : e i.val < M := by
    have h := (he i.val).trans (mul_le_mul (le_max_left ..) (by gcongr; exact i.property)
      (by positivity) (le_max_right ..) : K * (1 + |i.val.1.val.im|) ≤ max K 0 * (1 + T))
    exact_mod_cast (show (e i.val : ℝ) < M by linarith)
  have : Finite band := Finite.of_injective (fun i : band ↦ (⟨e i.val, heM i⟩ : Fin M))
    (fun i j h ↦ Subtype.ext (e.injective (congrArg Fin.val h)))
  let _ := Fintype.ofFinite band
  let u (j : J) (z : ℂ) := (f (rep j)).val (z - v (n j))
  have hd (j : J) : Differentiable ℂ (f j).val := differentiableOn_univ.mp (by simpa using (f j).property.2.1)
  refine ⟨u, fun j ↦ (hd _).comp (differentiable_id.sub_const _), fun i j ↦ ?_, fun A k ↦ ?_⟩
  · have h := hf (shift (n j) i) (rep j)
    simpa only [u, iteratedDeriv_comp_sub_const, rep, (shift_inj (n j)).eq_iff] using h
  · have bound (i : band) : ∃ C ≥ (0 : ℝ), ∀ z : ℂ, |z.re| ≤ A →
        (1 + ‖z‖) ^ k * ‖(f i.val).val z‖ ≤ C := by
      have bnd (m : ℕ) := (f i.val).property.2.2 (-|A|) |A| (by linarith [abs_nonneg A]) (subset_univ _) m
      obtain ⟨C₀, h₀⟩ := bnd 0
      obtain ⟨C₁, h₁⟩ := bnd k
      refine ⟨2 ^ (k - 1) * (max C₀ 0 + max C₁ 0), by positivity, fun z hz ↦ ?_⟩
      have hz' : z ∈ Complex.re ⁻¹' Icc (-|A|) |A| := abs_le.mp (hz.trans (le_abs_self A))
      have h0 : ‖(f i.val).val z‖ ≤ C₀ := by simpa using h₀ ⟨z, hz', rfl⟩
      have h1 : ‖z‖ ^ k * ‖(f i.val).val z‖ ≤ C₁ := by simpa [norm_mul] using h₁ ⟨z, hz', rfl⟩
      calc
        _ ≤ (2 ^ (k - 1) * (1 ^ k + ‖z‖ ^ k)) * ‖(f i.val).val z‖ :=
          mul_le_mul_of_nonneg_right (add_pow_le zero_le_one (norm_nonneg _) k) (norm_nonneg _)
        _ ≤ _ := by
          rw [one_pow, mul_assoc, add_mul, one_mul]
          exact mul_le_mul_of_nonneg_left (add_le_add (h0.trans (le_max_left ..))
            (h1.trans (le_max_left ..))) (by positivity)
    choose C hC hb using bound
    let A₀ := ∑ i : band, C i
    refine ⟨A₀ * (1 + T) ^ k, mul_nonneg (Finset.sum_nonneg fun i _ ↦ hC i) (by positivity), fun j z hz ↦ ?_⟩
    let i : band := ⟨rep j, hband j⟩
    let t := v (n j)
    have ht : t.re = 0 := by simp [t, v, zsmul_eq_mul, ← mul_assoc]
    have him : (rep j).1.val.im = j.1.val.im - t.im := Complex.sub_im ..
    have ht' : ‖t‖ ≤ |j.1.val.im| + T := by
      have ht1 := Complex.norm_le_abs_re_add_abs_im t
      have ht2 := abs_sub j.1.val.im (rep j).1.val.im
      rw [him, sub_sub_cancel] at ht2
      rw [ht, abs_zero, zero_add] at ht1
      exact ht1.trans (ht2.trans (add_le_add le_rfl (him ▸ hband j)))
    have hv : 1 + ‖z‖ ≤ (1 + ‖z - t‖) * ((1 + T) * (1 + |j.1.val.im|)) := by
      have h := norm_add_le (z - t) t
      rw [sub_add_cancel] at h
      calc
        _ ≤ (1 + ‖z - t‖) * (1 + ‖t‖) := by nlinarith [mul_nonneg (norm_nonneg (z - t)) (norm_nonneg t)]
        _ ≤ _ := by gcongr; nlinarith [mul_nonneg hT.le (abs_nonneg j.1.val.im)]
    have h := hb i (z - t) (by simpa [Complex.sub_re, ht] using hz)
    have hsum : C i ≤ A₀ := Finset.single_le_sum (fun r _ ↦ hC r) (Finset.mem_univ i)
    change (1 + ‖z‖) ^ k * ‖(f i.val).val (z - t)‖ ≤ _
    calc
      _ ≤ ((1 + ‖z - t‖) * ((1 + T) * (1 + |j.1.val.im|))) ^ k * ‖(f i.val).val (z - t)‖ := by gcongr
      _ = ((1 + ‖z - t‖) ^ k * ‖(f i.val).val (z - t)‖) * ((1 + T) ^ k * (1 + |j.1.val.im|) ^ k) := by
        rw [mul_pow, mul_pow]; ring
      _ ≤ _ := by
        simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right (h.trans hsum)
          (show 0 ≤ (1 + T) ^ k * (1 + |j.1.val.im|) ^ k by positivity))

/-- The factor 1 − (1 − H(s)/H(w))ᴺ is a multiple of H and equals one through order
N − 1 at w. Multiplication by it preserves all vanishing conditions at other sites. -/
private theorem finiteNuclearity_trace_jet_bounds_cardinal_growth_correct
    (H u : ℂ → ℂ) (hH : Differentiable ℂ H) (hu : Differentiable ℂ u)
    (w : ℂ) (hw : H w ≠ 0) (N : ℕ) :
    let f := fun z ↦ (1 - (1 - (H w)⁻¹ * H z) ^ N) * u z
    Differentiable ℂ f ∧ (∀ z, analyticOrderAt H z ≤ analyticOrderAt f z) ∧
      (∀ z, analyticOrderAt u z ≤ analyticOrderAt f z) ∧
      ∀ k < N, iteratedDeriv k f w = iteratedDeriv k u w := by
  intro f
  let E := fun z ↦ 1 - (H w)⁻¹ * H z
  have hE : Differentiable ℂ E := (hH.const_mul _).const_sub 1
  have hP : Differentiable ℂ (fun z ↦ 1 - E z ^ N) := (hE.pow N).const_sub 1
  refine ⟨hP.mul hu, fun z ↦ ?_, fun z ↦ ?_, fun k hk ↦ ?_⟩
  · let v := fun z ↦ ((H w)⁻¹ * ∑ i ∈ Finset.range N, E z ^ i) * u z
    have hv : Differentiable ℂ v := ((Differentiable.fun_sum fun i _ ↦ hE.pow i).const_mul _).mul hu
    have he : f = H * v := by
      funext s
      change (1 - E s ^ N) * u s = H s * (((H w)⁻¹ * _) * u s)
      rw [← geom_sum_mul_neg]
      dsimp only [E]
      ring
    rw [he, analyticOrderAt_mul (hH.analyticAt _) (hv.analyticAt _)]
    exact self_le_add_right ..
  · change _ ≤ analyticOrderAt ((fun s ↦ 1 - E s ^ N) * u) z
    rw [analyticOrderAt_mul (hP.analyticAt _) (hu.analyticAt _)]
    exact self_le_add_left ..
  · have h₁ : 1 ≤ analyticOrderAt E w := Order.one_le_iff_ne_zero.mpr
      ((hE.analyticAt w).analyticOrderAt_ne_zero.mpr (by simp [E, hw]))
    have hn : (N : ℕ∞) ≤ analyticOrderAt (E ^ N * u) w := by
      rw [analyticOrderAt_mul ((hE.pow N).analyticAt _) (hu.analyticAt _), analyticOrderAt_pow (hE.analyticAt _)]
      exact (show (N : ℕ∞) ≤ N • analyticOrderAt E w by simpa using nsmul_le_nsmul_right h₁ N).trans
        (self_le_add_right ..)
    have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (((hE.pow N).mul hu).analyticAt w)).mp hn k hk
    have he : f = u - E ^ N * u := by funext s; change (1 - E s ^ N) * u s = u s - E s ^ N * u s; ring
    rw [he, iteratedDeriv_sub hu.contDiff.contDiffAt ((hE.pow N).mul hu).contDiff.contDiffAt, hz, sub_zero]

/-- The jet correction costs only polynomial weights in the centre and the argument.
The degree N is fixed for the whole Euler fibre. -/
private theorem finiteNuclearity_trace_jet_bounds_cardinal_growth_correct_bound {J : Type*}
    (H : ℂ → ℂ) (c : J → ℂ) (w : J → ℝ) (hw : ∀ j, 1 ≤ w j) (u : J → ℂ → ℂ)
    (hH : ∀ A : ℝ, ∃ (n : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : ℂ, |z.re| ≤ A → ‖H z‖ ≤ C * (1 + ‖z‖) ^ n)
    (hc : ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ j, ‖c j‖ ≤ C * w j ^ k)
    (hu : ∀ A : ℝ, ∀ k : ℕ, ∃ C ≥ (0 : ℝ), ∀ j (z : ℂ), |z.re| ≤ A →
      (1 + ‖z‖) ^ k * ‖u j z‖ ≤ C * w j ^ k) (N : ℕ) (A : ℝ) (k : ℕ) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ j (z : ℂ), |z.re| ≤ A →
      (1 + ‖z‖) ^ k * ‖(1 - (1 - c j * H z) ^ N) * u j z‖ ≤ C * w j ^ m := by
  obtain ⟨r, D, hD, hd⟩ := hc
  obtain ⟨l, C, hC, h⟩ := hH A
  obtain ⟨B₀, hB, hb⟩ := hu A (k + l * N)
  let K := 1 + (1 + D * C) ^ N
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨r * N + (k + l * N), K * B₀, mul_nonneg hK hB, fun j z hz ↦ ?_⟩
  let s := 1 + ‖z‖
  have hs : 1 ≤ s := by dsimp [s]; linarith [norm_nonneg z]
  let v := w j ^ r * s ^ l
  have hv : 1 ≤ v := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (hw j)) (one_le_pow₀ hs)
  have h₁ : ‖1 - c j * H z‖ ≤ (1 + D * C) * v := calc
    _ ≤ 1 + ‖c j‖ * ‖H z‖ := by simpa only [norm_one, norm_mul] using norm_sub_le (1 : ℂ) (c j * H z)
    _ ≤ v + (D * w j ^ r) * (C * s ^ l) := add_le_add hv (mul_le_mul (hd j) (h z hz) (norm_nonneg _)
      (mul_nonneg hD (pow_nonneg (zero_le_one.trans (hw j)) _)))
    _ = _ := by dsimp [v]; ring
  have h₂ : ‖1 - (1 - c j * H z) ^ N‖ ≤ K * v ^ N := calc
    _ ≤ 1 + ‖1 - c j * H z‖ ^ N := by simpa only [norm_one, norm_pow] using norm_sub_le (1 : ℂ) ((1 - c j * H z) ^ N)
    _ ≤ v ^ N + ((1 + D * C) * v) ^ N := add_le_add (one_le_pow₀ hv) (pow_le_pow_left₀ (norm_nonneg _) h₁ _)
    _ = _ := by rw [mul_pow (1 + D * C) v]; dsimp only [K]; ring
  change s ^ k * _ ≤ _
  rw [norm_mul]
  calc
    _ ≤ s ^ k * ((K * v ^ N) * ‖u j z‖) := by gcongr
    _ = (K * w j ^ (r * N)) * (s ^ (k + l * N) * ‖u j z‖) := by dsimp [v]; rw [mul_pow, pow_add, pow_mul, pow_mul]; ring
    _ ≤ (K * w j ^ (r * N)) * (B₀ * w j ^ (k + l * N)) := mul_le_mul_of_nonneg_left (hb j z hz)
      (mul_nonneg hK (pow_nonneg (zero_le_one.trans (hw j)) _))
    _ = _ := by rw [pow_add]; ring

open Classical in
/-- Correct translated Euler cardinal functions by the reflected generator before lifting
them to the polar image. The uniform bound on the Euler orders fixes one correction degree. -/
private theorem finiteNuclearity_trace_jet_bounds_cardinal_growth_interpolants (R H : ℂ → ℂ)
    (hH : Differentiable ℂ H) (N : ℕ) :
    let J := Σ z : {z : ℂ // 0 < analyticOrderAt R z}, Fin (analyticOrderAt R z.val).toNat
    ∀ (u : J → ℂ → ℂ), (∀ j, Differentiable ℂ (u j)) →
    (∀ i j, iteratedDeriv i.2.val (u j) i.1.val = if i = j then 1 else 0) →
    (∀ j : J, j.2.val < N ∧ H j.1.val ≠ 0) →
    (∀ A : ℝ, ∃ (n : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : ℂ, |z.re| ≤ A → ‖H z‖ ≤ C * (1 + ‖z‖) ^ n) →
    (∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ j : J, ‖(H j.1.val)⁻¹‖ ≤ C * (1 + |j.1.val.im|) ^ k) →
    (∀ A : ℝ, ∀ k : ℕ, ∃ C ≥ (0 : ℝ), ∀ j (z : ℂ), |z.re| ≤ A →
      (1 + ‖z‖) ^ k * ‖u j z‖ ≤ C * (1 + |j.1.val.im|) ^ k) →
    ∃ f : J → B, (∀ j z, analyticOrderAt H z ≤ analyticOrderAt (f j).val z) ∧
      (∀ i j, iteratedDeriv i.2.val (f j).val i.1.val = if i = j then 1 else 0) ∧
      ∀ q : Seminorm ℂ B, Continuous q →
        ∃ (m : ℕ) (C : ℝ), ∀ j, q (f j) ≤ C * (1 + |j.1.val.im|) ^ m := by
  intro J u hu hjet hN hg hi hb
  let w (j : J) := 1 + |j.1.val.im|
  have hw (j : J) : 1 ≤ w j := le_add_of_nonneg_right (abs_nonneg _)
  let c (j : J) := (H j.1.val)⁻¹
  let v (j : J) (z : ℂ) := (1 - (1 - c j * H z) ^ N) * u j z
  have hv (j : J) := finiteNuclearity_trace_jet_bounds_cardinal_growth_correct H (u j) hH (hu j)
    j.1.val (hN j).2 N
  have bounds := finiteNuclearity_trace_jet_bounds_cardinal_growth_correct_bound H c w hw u hg hi hb N
  have mem (j : J) : v j ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
    refine ⟨fun z hz ↦ (hz (mem_univ _)).elim, (hv j).1.differentiableOn, fun a b _ _ k ↦ ?_⟩
    obtain ⟨m, C, _, h⟩ := bounds (|a| + |b|) k
    refine ⟨C * w j ^ m, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖z ^ k * v j z‖ ≤ _
    rw [norm_mul, norm_pow]
    refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z)
      (le_add_of_nonneg_left zero_le_one) k) (norm_nonneg _)).trans (h j z ?_)
    exact abs_le.mpr ⟨by linarith [hz.1, neg_abs_le a, abs_nonneg b],
      by linarith [hz.2, le_abs_self b, abs_nonneg a]⟩
  let f (j : J) : B := ⟨v j, mem j⟩
  refine ⟨f, fun j ↦ (hv j).2.1, fun i j ↦ ?_,
    finiteNuclearity_trace_jet_bounds_cardinal_growth_seminorm w hw f bounds⟩
  by_cases he : i.1 = j.1
  · change iteratedDeriv i.2.val (v j) i.1.val = _
    apply Eq.trans _ (hjet i j)
    exact (congrArg (fun z : ℂ ↦ iteratedDeriv i.2.val (v j) z = iteratedDeriv i.2.val (u j) z)
      (congrArg Subtype.val he)).mpr ((hv j).2.2.2 _ (hN i).1)
  · rw [ite_eq_right (fun h ↦ he (congrArg Sigma.fst h))]
    have ho : ((i.2.val + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (u j) i.1.val := by
      apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((hu j).analyticAt _)).mpr
      intro n hn
      let l : J := ⟨i.1, n, (Nat.le_of_lt_succ hn).trans_lt i.2.isLt⟩
      have hlj : l ≠ j := by
        intro h
        have h' : l.1 = j.1 := congrArg (fun t : J ↦ t.1) h
        exact he h'
      exact (hjet l j).trans (ite_eq_right hlj)
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((hv j).1.analyticAt _)).mp
      (ho.trans ((hv j).2.2.1 _)) _ (Nat.lt_succ_self _)

open Classical in
/-- Polynomial growth of the cardinal Euler jets in each continuous seminorm of the
polar quotient. The constants and exponent may depend on the seminorm. A construction
of interpolants in the polar Mellin image with polynomial strip bounds suffices,
since the jets separate the quotient. This estimate is independent of the test action. -/
private theorem finiteNuclearity_trace_jet_bounds_cardinal_growth
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    let D := finiteNuclearityDenominator χ p
    let Q := Θ₀(χ) ⧸ D
    let R := reciprocalPartialHeckeEulerProduct χ (Sₚ(p))
    let J := Σ z : {z : ℂ // 0 < analyticOrderAt R z}, Fin (analyticOrderAt R z.val).toNat
    ∀ (d : J → StrongDual ℂ Q) (b : J → Q),
      (∀ j x, d j (D.mkQ x) = iteratedDeriv j.2.val ((Z(χ, τ, hτ)) x).val j.1.val) →
      (∀ i j, d i (b j) = if i = j then 1 else 0) →
      ∀ q : Seminorm ℂ Q, Continuous q →
        ∃ (m : ℕ) (C : ℝ), ∀ j, q (b j) ≤ C * (1 + |j.1.val.im|) ^ m := by
  classical
  intro D Q R J d b hd hb q hq
  let Zf := Z(χ, τ, hτ)
  choose a ha using fun j ↦ D.mkQ_surjective (b j)
  have jet (i j : J) : iteratedDeriv i.2.val (Zf (a j)).val i.1.val = if i = j then 1 else 0 :=
    (hd i (a j)).symm.trans ((congrArg (d i) (ha j)).trans (hb i j))
  obtain ⟨e, K, he⟩ := finiteNuclearity_trace_jet_bounds_enumeration χ p
  obtain ⟨T, hT, hper⟩ := finiteNuclearity_trace_jet_bounds_cardinal_growth_period χ p
  obtain ⟨u, hu, hjet, hbound⟩ := finiteNuclearity_trace_jet_bounds_cardinal_growth_translates R T hT hper
    e K (fun j ↦ (he j).2.2) (fun j ↦ Zf (a j)) jet
  obtain ⟨H, hH, hord, hstrip, k, C, hC, hinv⟩ := finiteNuclearity_trace_jet_bounds_cardinal_growth_multiplier χ τ hτ
  obtain ⟨f, hf, hfj, hfq⟩ := finiteNuclearity_trace_jet_bounds_cardinal_growth_interpolants R H hH
    (Module.finrank ℚ F + 1) u hu hjet
    (fun j ↦ ⟨Nat.lt_succ_of_le (he j).2.1, (hinv _ (he j).1).1⟩)
    hstrip ⟨k, C, hC, fun j ↦ (hinv _ (he j).1).2⟩ hbound
  have lift (j : J) : ∃ x, Zf x = f j := by
    apply (specDenom_range_mem χ τ hτ _).mpr
    apply (specDenom_mem_div _ _).mp
    apply (finiteNuclearity_trace_divisible _ _).mpr
    intro z n hn
    have h := hn.trans_le ((hord z).trans (hf j z))
    have hol : Differentiable ℂ (f j).val := differentiableOn_univ.mp (by simpa using (f j).property.2.1)
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hol.analyticAt z)).mp
      ((ENat.add_one_le_iff (ENat.natCast_ne_top n)).mpr h) n (Nat.lt_succ_self n)
  choose x hx using lift
  obtain ⟨d₀, _, hd₀, _, sep⟩ := finiteNuclearity_trace_jets χ τ hτ p
  have eqd (i : J) : d₀ i = d i := ContinuousLinearMap.ext fun y ↦ by
    obtain ⟨v, rfl⟩ := D.mkQ_surjective y
    exact (hd₀ i v).trans (hd i v).symm
  have eqb (j : J) : D.mkQ (x j) = b j := by
    apply sub_eq_zero.mp
    apply sep
    intro i
    rw [eqd, map_sub, hd, hb]
    exact sub_eq_zero.mpr ((congrArg (fun g : B ↦ iteratedDeriv i.2.val g.val i.1.val) (hx j)).trans (hfj i j))
  obtain ⟨r, hr, hdom⟩ := Seminorm.exists_le_comp_of_isInducing
    (p := q.comp D.mkQ) (hq.comp D.mkQL.continuous) (f := Zf.toLinearMap)
    (exists_polarThetaNuclearityAction_mellin_closedEmbedding F χ τ hτ).isInducing
  obtain ⟨m, C₀, h⟩ := hfq r hr
  refine ⟨m, C₀, fun j ↦ ?_⟩
  rw [← eqb j]
  exact (hdom (x j)).trans ((congrArg r (hx j)).le.trans (h j))

-- TODO(paper-gap): The cited §7.1.4.3 concerns the entire comparison space.
-- To apply the rapid-decay argument on this quotient, one needs bounds in its
-- own topology for the functionals and the biorthogonal vectors.

open Classical in
/-- Uniform rescaling of the finite orbital jet expansion. The scaled coordinate
vectors must lie in one Banach disc of the polar quotient, while one continuous
seminorm bounds the correspondingly rescaled rows of the test action. The residual
coefficients must decrease rapidly in a single enumeration (allowing unused indices).
The comparison jets in §7.1.4.3 give biorthogonality without these simultaneous bounds.
A periodic interpolation estimate in the topology of the polar quotient would supply them. -/
private theorem finiteNuclearity_trace_jet_bounds (p : HeightOneSpectrum (𝓞 ℚ)) (φ : 𝒟) :
    let D := finiteNuclearityDenominator χ p
    let Q := Θ₀(χ) ⧸ D
    letI : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
    let R := reciprocalPartialHeckeEulerProduct χ (Sₚ(p))
    let J := Σ z : {z : ℂ // 0 < analyticOrderAt R z}, Fin (analyticOrderAt R z.val).toNat
    ∀ (d : J → StrongDual ℂ Q) (b : J → Q),
      (∀ j x, d j (D.mkQ x) = iteratedDeriv j.2.val ((Z(χ, τ, hτ)) x).val j.1.val) →
      (∀ i j, d i (b j) = if i = j then 1 else 0) →
      ∃ (e : J ↪ ℕ) (a c : J → ℂˣ) (B₀ : Set Q) (q : Seminorm ℂ Q),
        IsBanachDisc B₀ ∧ (∀ j, (a j : ℂ) • b j ∈ B₀) ∧ Continuous q ∧
        (∀ j x, ‖((c j : ℂ) * (a j : ℂ))⁻¹ * d j (D.mkQ (Aθ(φ) x))‖ ≤ q (D.mkQ x)) ∧
        ∀ k : ℕ, ∃ C : ℝ, ∀ j, ‖(c j : ℂ)‖ * ((e j : ℝ) + 1) ^ k ≤ C := by
  classical
  intro D Q R J d b hd hb
  obtain ⟨hclosed, hmaps⟩ := finiteNuclearityDenominator_closed_invariant χ τ hτ p φ
  have hQ : IsFrechetTVS Q := finiteNuclearity_trace_jet_bounds_frechet (Z(χ, τ, hτ))
    (exists_polarThetaNuclearityAction_mellin_closedEmbedding F χ τ hτ)
    (schwartzBergman_frechet univ isOpen_univ ordConnected_univ univ_nonempty) D hclosed
  let M := nuclearityTestMellin χ φ
  have hM : Differentiable ℂ M := archNuclearityDenominator_closed_invariant_multiplier χ φ
  have decay (k : ℕ) : ∃ C : ℝ, ∀ w : ℂ, w.re ∈ Icc (-1 : ℝ) 1 →
      ‖M w‖ * (1 + |w.im|) ^ k ≤ C := by
    obtain ⟨C, _, h⟩ := spectralBoundary_globalStrip hM.continuous
      (spectralNuclearity_trace_vertical_decay χ φ (-1) 1 (by norm_num)) k
    exact ⟨C, h⟩
  obtain ⟨r, hr, hcircle, hrapid⟩ := finiteNuclearity_trace_jet_bounds_envelope M hM.continuous decay
  have enumeration : ∃ (e : J ↪ ℕ) (K : ℝ), ∀ j, j.1.val.re = 0 ∧
      j.2.val ≤ Module.finrank ℚ F ∧ (e j : ℝ) + 1 ≤ K * (1 + |j.1.val.im|) :=
    finiteNuclearity_trace_jet_bounds_enumeration (F := F) χ p
  obtain ⟨e, K, hcode⟩ := enumeration
  let T₀ := D.mapQ D (Aθ(φ)).toLinearMap (fun _ hx ↦ hmaps hx)
  let T : Q →L[ℂ] Q := ⟨T₀, (Submodule.isQuotientMap_mkQ D).continuous_iff.mpr
    ((Submodule.isQuotientMap_mkQ D).continuous.comp (Aθ(φ)).continuous)⟩
  let row (j : J) := (d j).comp T
  have hrow (x : Q) : ∃ C : ℝ, ∀ j, ‖row j x‖ ≤ r j.1.val ^ 2 * C := by
    obtain ⟨y, rfl⟩ := D.mkQ_surjective x
    let f := (Z(χ, τ, hτ)) y
    obtain ⟨C, hC⟩ := finiteNuclearity_trace_jet_bounds_cauchy M hM r hcircle (Module.finrank ℚ F) f
    refine ⟨C, fun j ↦ ?_⟩
    change ‖d j (D.mkQ (Aθ(φ) y))‖ ≤ _
    have hprod : ((Z(χ, τ, hτ)) ((Aθ(φ)) y)).val = M * f.val :=
      funext ((exists_polarThetaNuclearityAction χ τ hτ φ).choose_spec.1 y)
    rw [hd, hprod]
    exact hC _ _ (hcode j).1 (hcode j).2.1
  have hcol := finiteNuclearity_trace_jet_bounds_cardinal_growth χ τ hτ p d b hd hb
  let : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  have rescaled : ∃ (a : J → ℂˣ) (disc : Set Q) (q : Seminorm ℂ Q),
      IsBanachDisc disc ∧ (∀ j, (a j : ℂ) • b j ∈ disc) ∧ Continuous q ∧
      (∀ j x, ‖((a j : ℂ) * (a j : ℂ))⁻¹ * row j x‖ ≤ q x) ∧
      ∀ k : ℕ, ∃ C : ℝ, ∀ j, ‖(a j : ℂ)‖ * ((e j : ℝ) + 1) ^ k ≤ C :=
    finiteNuclearity_trace_jet_bounds_rescale (I := J) (E := Q)
    hQ e (fun j ↦ 1 + |j.1.val.im|) (fun j ↦ r j.1.val) (fun j ↦ by positivity)
    (fun j ↦ hr _) K (fun j ↦ (hcode j).2.2)
    (fun k ↦ (hrapid k).imp fun C h j ↦ h _ (hcode j).1) b row hcol hrow
  obtain ⟨a, disc, q, hB, hv, hq, hrows, hc⟩ := rescaled
  exact ⟨e, a, a, disc, q, hB, hv, hq, fun j x ↦ hrows j (D.mkQ x), hc⟩

/-- Paper: Theorem 7.4.2.1(2), p. 367.
The operator induced on the finite orbital quotient is of order zero. Its trace sums
the test Mellin transform over the zeros of the reciprocal partial Euler product,
counting collisions with their full order. -/
theorem finiteNuclearity_trace (p : HeightOneSpectrum (𝓞 ℚ)) (φ : 𝒟) :
    let D := finiteNuclearityDenominator χ p
    let Q := Θ₀(χ) ⧸ D
    letI instFiniteUniformSec4 : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
    let R := reciprocalPartialHeckeEulerProduct χ (Sₚ(p))
    let zeros := {z : ℂ // 0 < analyticOrderAt R z}
    let term := fun z : zeros ↦
      ((analyticOrderAt R z.val).toNat : ℂ) * nuclearityTestMellin χ φ z.val
    ∃ T : Q →L[ℂ] Q,
      (∀ f : Θ₀(χ), T (D.mkQ f) = D.mkQ (Aθ(φ) f)) ∧
      IsStronglyNuclearOperator T ∧ Summable (fun z ↦ ‖term z‖) ∧
      ∀ r : NuclearPresentation T,
        HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) (∑' z, term z) := by
  classical
  intro D Q R zeros term
  let : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  let : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  obtain ⟨hclosed, hmaps⟩ := finiteNuclearityDenominator_closed_invariant χ τ hτ p φ
  let T₀ : Q →ₗ[ℂ] Q := D.mapQ D (Aθ(φ)).toLinearMap (fun _ hx ↦ hmaps hx)
  let T : Q →L[ℂ] Q := ⟨T₀, (Submodule.isQuotientMap_mkQ D).continuous_iff.mpr
    ((Submodule.isQuotientMap_mkQ D).continuous.comp (Aθ(φ)).continuous)⟩
  have hT (x : Θ₀(χ)) : T (D.mkQ x) = D.mkQ (Aθ(φ) x) := rfl
  have hQ := finiteNuclearity_trace_quotient_nuclear (Z(χ, τ, hτ))
    (exists_polarThetaNuclearityAction_mellin_closedEmbedding F χ τ hτ).isEmbedding
    spectralJet_sb_nuclear D hclosed
  choose d b hd hb hsep using finiteNuclearity_trace_jets χ τ hτ p
  choose e a c disc q hB hv hq hrow hr using
    finiteNuclearity_trace_jet_bounds χ τ hτ p φ d b hd hb
  let M := nuclearityTestMellin χ φ
  let m (z : zeros) := (analyticOrderAt R z.val).toNat
  have diag (j : Σ z, Fin (m z)) : d j (T (b j)) = M j.1.val :=
    finiteNuclearity_trace_diagonal D.mkQ D.mkQ_surjective (Aθ(φ)) T hT
      (fun x ↦ ((Z(χ, τ, hτ)) x).val) (fun x z ↦
        (((Z(χ, τ, hτ)) x).property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' mem_univ))
      M (archNuclearityDenominator_closed_invariant_multiplier χ φ)
      (fun x ↦ funext ((exists_polarThetaNuclearityAction χ τ hτ φ).choose_spec.1 x))
      Subtype.val m d b hd hb j
  have hrow' (j) (x : Q) : ‖((c j : ℂ) * (a j : ℂ))⁻¹ * d j (T x)‖ ≤ q x := by
    obtain ⟨y, rfl⟩ := D.mkQ_surjective x
    exact hrow j y
  refine ⟨T, hT, ?_⟩
  exact finiteNuclearity_trace_of_bounds T hQ m (fun z ↦ M z.val) d b hb hsep diag e a c disc q
    hB hv hq hrow' hr

end Orbital

section Archimedean

open Classical

local notation "RealPlaces" => {v : InfinitePlace F // v.IsReal}
local notation "ComplexPlaces" => {v : InfinitePlace F // v.IsComplex}
local notation "Coordinates" => (RealPlaces → ℝ) × (ComplexPlaces → ℂ)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)

variable (F) in
/-- Paper: Equation (7.4.3.1), p. 368.
Finite sums of adelic tensors have flat archimedean factors and arbitrary finite
factors. When required, each archimedean factor has additive integral zero.
Deviation: Uses the adelic tensor realization of §2.1.3 and the flat jet
conditions from §5.3.3. The tensor image carries the subspace topology from the
adelic Schwartz space. The display on p. 368 writes the projective tensor topology. -/
def globalArchimedeanFlatTests (requireArchMoment : Prop := False) : Submodule ℂ ℬ(𝔸[F]) :=
  let coordinates (x : InfiniteAdeleRing F) : Coordinates :=
    (fun v ↦ InfinitePlace.Completion.ringEquivRealOfIsReal v.property (x v.val),
      fun v ↦ InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property (x v.val))
  let tensor := (adeleSchwartz_inductiveTensor_equiv F).choose
  Submodule.span ℂ {test | ∃ (f : ℬ(InfiniteAdeleRing F))
    (g : ℬ(FiniteAdeleRing (𝓞 F) F))
    (h : archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)),
    (∀ x : InfiniteAdeleRing F, f (Multiplicative.ofAdd x) = h.val (coordinates x)) ∧
      (requireArchMoment → (∫ u : Coordinates, h.val u) = 0) ∧
      tensor (f ⊗ₜ[ℂ] g) = test}

variable (F) in
/-- Paper: Equation (7.4.3.1), p. 368.
The archimedean-flat tensor image is closed in the adelic Schwartz topology,
including when the archimedean integral of each tensor factor must vanish. -/
theorem globalArchimedeanFlatTests_isClosed (requireArchMoment : Prop) :
    IsClosed (globalArchimedeanFlatTests F requireArchMoment : Set ℬ(𝔸[F])) := by
  classical
  let E := ℬ(InfiniteAdeleRing F)
  let Ef := ℬ(FiniteAdeleRing (𝓞 F) F)
  let flat := archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)
  let I : SchwartzMap Coordinates ℂ →L[ℂ] ℂ := SchwartzMap.integralCLM ℂ volume
  let flatWithMoment := flat ⊓ ⨅ _ : requireArchMoment, I.ker
  have hP : IsClosed (flatWithMoment : Set (SchwartzMap Coordinates ℂ)) := by
    simpa only [flatWithMoment, Submodule.coe_inf, Submodule.coe_iInf] using
      (archimedeanFlatSchwartz_isClosed (ι := RealPlaces) (κ := ComplexPlaces)).inter
        (isClosed_iInter fun _ : requireArchMoment ↦ I.isClosed_ker)
  obtain ⟨J, hJ⟩ := archimedeanSchwartzBruhat_equiv (F := F)
  let K := flatWithMoment.comap J.symm.toLinearMap
  have hK : IsClosed (K : Set E) := hP.preimage J.symm.continuous
  let : T2Space E := J.symm.toHomeomorph.isEmbedding.t2Space
  let : T2Space Ef := schwartzBruhat_t2_of_stages
  let : T2Space (E ⧸ K) := inferInstance
  let : PolynormableSpace ℂ (E ⧸ K) := polynormableSpace_quotient K
  let q : InductiveTensor E Ef →L[ℂ] InductiveTensor (E ⧸ K) Ef :=
    ⟨inductiveTensorMap K.mkQ LinearMap.id, inductiveTensorMap_continuous K.mkQL (ContinuousLinearMap.id ℂ Ef)⟩
  let e := (adeleSchwartz_inductiveTensor_equiv F).choose
  let D := globalArchimedeanFlatTests F requireArchMoment
  have hr : q.ker = (K.subtype.rTensor Ef).range := rTensor_mkQ Ef K
  have hmem (f : E) : f ∈ K ↔ ∃ h : flat,
      (∀ x : InfiniteAdeleRing F, f (Multiplicative.ofAdd x) =
        h.val (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) ∧
      (requireArchMoment → (∫ u : Coordinates, h.val u) = 0) := by
    change J.symm f ∈ flat ⊓ ⨅ _ : requireArchMoment, I.ker ↔ _
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    constructor
    · rintro ⟨hf, hi⟩
      exact ⟨⟨J.symm f, hf⟩, fun x ↦ ((congrArg (fun g : E ↦ g (Multiplicative.ofAdd x))
        (J.apply_symm_apply f)).symm.trans (hJ _ _)), hi⟩
    · rintro ⟨h, hf, hi⟩
      have he : f = J h.val := Subtype.ext (funext fun x ↦ (hf x.toAdd).trans (hJ _ _).symm)
      rw [he, J.symm_apply_apply]
      exact ⟨h.property, hi⟩
  let insertFlat : (K ⊗[ℂ] Ef) →ₗ[ℂ] ℬ(𝔸[F]) := e.toLinearMap.comp (K.subtype.rTensor Ef)
  have hB (z : K ⊗[ℂ] Ef) : insertFlat z ∈ D := by
    induction z using TensorProduct.inductionOn with
    | tmul f g =>
      obtain ⟨h, hf, hi⟩ := (hmem f.val).mp f.property
      exact Submodule.subset_span ⟨f.val, g, h, hf, hi, rfl⟩
    | add u v hu hv => exact (map_add insertFlat u v).symm ▸ D.add_mem hu hv
  have hD : D = (q.comp e.symm.toContinuousLinearMap).ker := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨f, g, h, hf, hi, rfl⟩
      have hfK := (hmem f).mpr ⟨h, hf, hi⟩
      let z : InductiveTensor E Ef := f ⊗ₜ[ℂ] g
      refine (congrArg q (e.symm_apply_apply z)).trans ?_
      change K.mkQ f ⊗ₜ[ℂ] g = 0
      have hf0 : K.mkQ f = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hfK
      rw [hf0, TensorProduct.zero_tmul]
    · intro x hx
      have hh : e.symm x ∈ q.ker := hx
      rw [hr] at hh
      obtain ⟨z, hz⟩ := hh
      have he : insertFlat z = x := (congrArg (fun v : InductiveTensor E Ef ↦ e v) hz).trans (e.apply_symm_apply x)
      exact he ▸ hB z
  change IsClosed (D : Set ℬ(𝔸[F]))
  rw [hD]
  exact (q.comp e.symm.toContinuousLinearMap).isClosed_ker

/-- A flat archimedean Schwartz function vanishes at the origin, which meets a wall. -/
private theorem globalArchimedeanFlatTests_zero_moments_flat
    (h : archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)) :
    h.val (0 : Coordinates) = 0 := by
  have hw : (∃ i, (0 : Coordinates).1 i = 0) ∨ (∃ j, (0 : Coordinates).2 j = 0) := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    rcases w.isReal_or_isComplex with hr | hc
    · exact Or.inl ⟨⟨w, hr⟩, rfl⟩
    · exact Or.inr ⟨⟨w, hc⟩, rfl⟩
  have hk := Submodule.mem_iInf _ |>.mp h.property ⟨0, hw⟩
  have hk := Submodule.mem_iInf _ |>.mp hk 0
  have hk := Submodule.mem_iInf _ |>.mp hk (fun i => Fin.elim0 i)
  have := LinearMap.mem_ker.mp hk
  simpa using this

/-- Paper: Equation (7.4.3.1), p. 368.
Archimedean flatness kills evaluation at the adelic origin. Within the flat space,
the other zero-moment condition is the vanishing of the Fourier value at the origin. -/
theorem globalArchimedeanFlatTests_zero_moments (f : ℬ(𝔸[F]))
    (_hf : f ∈ globalArchimedeanFlatTests F) :
    f (Multiplicative.ofAdd 0) = 0 ∧
      (f ∈ adelePolarSubspace F ↔ adeleSchwartzFourier (F := F) f (Multiplicative.ofAdd 0) = 0) := by
  have h0 : f (Multiplicative.ofAdd 0) = 0 := by
    let ev : ℬ(𝔸[F]) →ₗ[ℂ] ℂ :=
      { toFun := fun f ↦ f (Multiplicative.ofAdd 0)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    change ev f = 0
    have hf : f ∈ LinearMap.ker ev := by
      refine (Submodule.span_le.mpr ?_) _hf
      rintro _ ⟨g₁, g₂, h, hx, -, rfl⟩
      change (adeleSchwartz_inductiveTensor_equiv F).choose (g₁ ⊗ₜ[ℂ] g₂) (Multiplicative.ofAdd 0) = 0
      rw [(adeleSchwartz_inductiveTensor_equiv F).choose_spec g₁ g₂ 0]
      have : g₁ (Multiplicative.ofAdd (0 : InfiniteAdeleRing F)) = 0 := by
        rw [hx 0]
        convert globalArchimedeanFlatTests_zero_moments_flat h using 2
        refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_)
        · exact map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal v.property)
        · exact map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property)
      exact mul_eq_zero_of_left this _
    exact LinearMap.mem_ker.mp hf
  refine ⟨h0, ?_⟩
  rw [mem_adelePolarSubspace]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h0, h⟩⟩

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

/-- Paper: Equation (7.4.3.1), p. 368.
The denominator uses archimedean-flat factors. On the trivial norm-one component
each factor has zero additive integral, equivalently zero local Fourier value at zero.
Deviation: Implements the prose Fourier-moment condition. On a nontrivial norm-one
isotype the moment restriction can be imposed on representatives, since the two
polar functionals are trivial-isotypic. -/
def archNuclearityDenominator : Submodule ℂ (Θ₀(χ)) :=
  Submodule.span ℂ {x : Θ₀(χ) | ∃ f : P,
    f.val ∈ globalArchimedeanFlatTests F (ω(χ) = 1) ∧ x = Submodule.Quotient.mk f}

section FlatPolarImage

local notation "Coord" =>
  ({v : InfinitePlace F // v.IsReal} → ℝ) × ({v : InfinitePlace F // v.IsComplex} → ℂ)
local notation "Flat" =>
  archimedeanFlatSchwartz (ι := {v : InfinitePlace F // v.IsReal}) (κ := {v : InfinitePlace F // v.IsComplex})
local notation "coord" => InfiniteAdeleRing.ringEquiv_mixedSpace F

/-- The archimedean Schwartz functions with flat coordinate realizations. -/
private def archNuclearity_flatFactors : Submodule ℂ ℬ(InfiniteAdeleRing F) where
  carrier := {a | ∃ h : Flat, ∀ x : InfiniteAdeleRing F, a (Multiplicative.ofAdd x) = h.val (coord x)}
  zero_mem' := ⟨0, fun _ ↦ rfl⟩
  add_mem' := by
    rintro a b ⟨h, hh⟩ ⟨k, hk⟩
    refine ⟨h + k, fun x ↦ ?_⟩
    exact congrArg₂ (· + ·) (hh x) (hk x)
  smul_mem' := by
    rintro r a ⟨h, hh⟩
    exact ⟨r • h, fun x ↦ congrArg (r • ·) (hh x)⟩

/-- Coordinatewise multiplication by units preserves every archimedean wall
and hence also the vanishing of every jet along those walls. -/
private theorem archNuclearity_flatFactors_translate (u : (InfiniteAdeleRing F)ˣ)
    (a : ℬ(InfiniteAdeleRing F)) (ha : a ∈ archNuclearity_flatFactors) :
    schwartzBruhatUnitTranslate u a ∈ archNuclearity_flatFactors := by
  obtain ⟨h, hh⟩ := ha
  let d := Units.map (coord).toMonoidHom u⁻¹
  let L₀ : Coord ≃ₗ[ℝ] Coord :=
    { LinearMap.mulLeft ℝ (d : Coord) with
      invFun := fun x ↦ (↑d⁻¹ : Coord) * x
      left_inv := fun x ↦ by
        change (↑d⁻¹ : Coord) * ((d : Coord) * x) = x
        rw [← mul_assoc, Units.inv_mul, one_mul]
      right_inv := fun x ↦ by
        change (d : Coord) * ((↑d⁻¹ : Coord) * x) = x
        rw [← mul_assoc, Units.mul_inv, one_mul] }
  let L := L₀.toContinuousLinearEquiv
  let k := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L h.val
  have hk : k ∈ Flat := by
    have hf := h.property
    simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker, IsLinearMap.mk'_apply] at hf ⊢
    rintro ⟨x, hx⟩ n v
    have hx' : (∃ i, (L x).1 i = 0) ∨ ∃ j, (L x).2 j = 0 := by
      rcases hx with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact Or.inl ⟨i, by change (d : Coord).1 i * x.1 i = 0; rw [hi, mul_zero]⟩
      · exact Or.inr ⟨j, by change (d : Coord).2 j * x.2 j = 0; rw [hj, mul_zero]⟩
    change iteratedFDeriv ℝ n ((h.val : Coord → ℂ) ∘ L) x v = 0
    erw [L.toContinuousLinearMap.iteratedFDeriv_comp_right (h.val.smooth ⊤) x (i := n)
      (mod_cast le_top)]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    exact hf ⟨L x, hx'⟩ n (fun i ↦ L (v i))
  refine ⟨⟨k, hk⟩, fun x ↦ ?_⟩
  rw [schwartzBruhatUnitTranslate_apply, hh]
  change h.val (coord ((↑u⁻¹ : InfiniteAdeleRing F) * x)) = h.val ((d : Coord) * coord x)
  rw [map_mul]
  rfl


/-- Once finite mass-zero factors may be discarded modulo a submodule, the total
moment of a flat tensor sum can be imposed on one archimedean representative. -/
private theorem tensor_mem_flat_moment_sup
    {E W X : Type*} [AddCommGroup E] [AddCommGroup W] [AddCommGroup X]
    [Module ℂ E] [Module ℂ W] [Module ℂ X]
    (e : E ⊗[ℂ] W →ₗ[ℂ] X) (Uflat : Submodule ℂ E) (A K : Submodule ℂ X)
    (i : E →ₗ[ℂ] ℂ) (j : W →ₗ[ℂ] ℂ) (L : X →ₗ[ℂ] ℂ)
    (b₀ : W) (hb₀ : j b₀ = 1)
    (hL : ∀ a b, L (e (a ⊗ₜ[ℂ] b)) = i a * j b)
    (hA : ∀ a ∈ Uflat, i a = 0 → ∀ b, e (a ⊗ₜ[ℂ] b) ∈ A)
    (hK : ∀ a ∈ Uflat, ∀ b, j b = 0 → e (a ⊗ₜ[ℂ] b) ∈ A ⊔ K)
    {x : X} (hx : x ∈ Submodule.span ℂ {v | ∃ a ∈ Uflat, ∃ b, e (a ⊗ₜ[ℂ] b) = v})
    (hx₀ : L x = 0) : x ∈ A ⊔ K := by
  let u : E →ₗ[ℂ] X := e.comp ((TensorProduct.mk ℂ E W).flip b₀)
  have hu (a : E) : u a = e (a ⊗ₜ[ℂ] b₀) := rfl
  have H (x : X) (hx : x ∈ Submodule.span ℂ {v | ∃ a ∈ Uflat, ∃ b, e (a ⊗ₜ[ℂ] b) = v}) :
      ∃ a ∈ Uflat, i a = L x ∧ x - u a ∈ A ⊔ K := by
    refine Submodule.span_induction (p := fun x _ ↦ ∃ a ∈ Uflat, i a = L x ∧ x - u a ∈ A ⊔ K)
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, ha, b, rfl⟩
      refine ⟨j b • a, Uflat.smul_mem _ ha, ?_, ?_⟩
      · rw [map_smul, smul_eq_mul, hL, mul_comm]
      · have hj : j (b - j b • b₀) = 0 := by
          rw [map_sub, map_smul, hb₀, smul_eq_mul, mul_one, sub_self]
        have h := hK a ha (b - j b • b₀) hj
        simpa only [TensorProduct.tmul_sub, TensorProduct.tmul_smul, TensorProduct.smul_tmul', map_sub, hu] using h
    · exact ⟨0, Uflat.zero_mem, by rw [map_zero, map_zero], by simp⟩
    · rintro x y _ _ ⟨a, ha, hia, hxa⟩ ⟨b, hb, hib, hyb⟩
      refine ⟨a + b, Uflat.add_mem ha hb, by rw [map_add, map_add, hia, hib], ?_⟩
      rw [map_add, add_sub_add_comm]
      exact Submodule.add_mem _ hxa hyb
    · rintro c x _ ⟨a, ha, hia, hxa⟩
      refine ⟨c • a, Uflat.smul_mem c ha, by rw [map_smul, map_smul, hia], ?_⟩
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ c hxa
  obtain ⟨a, ha, hi, he⟩ := H x hx
  have haux : u a ∈ A ⊔ K := (show A ≤ A ⊔ K from le_sup_left) (hA a ha (hi.trans hx₀) b₀)
  have hsum := Submodule.add_mem _ he haux
  rwa [sub_add_cancel] at hsum


local notation "Aflat" => archNuclearity_flatFactors (F := F)
local notation "A₀(" χ ")" => globalArchimedeanFlatTests F (ω(χ) = 1)
local notation "A" => globalArchimedeanFlatTests F
local notation "K(" χ ")" => (homogeneousAdelicThetaLinearMap F (ω(χ))).ker
local notation "ArchTests" => ℬ(InfiniteAdeleRing F)
local notation "FiniteTests" => ℬ(FiniteAdeleRing (𝓞 F) F)
local notation "tensor" => (adeleSchwartz_inductiveTensor_equiv F).choose
local notation "hatL" => (ContinuousLinearMap.snd ℂ ℂ ℂ).toLinearMap.comp
  ((adelePolarValues_isLinear (F := F)).mk' adelePolarValues)

private theorem archNuclearityDenominator_mem_restricted
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (x : Θ₀(χ)) :
    x ∈ archNuclearityDenominator χ ↔
      ∃ f : P, f.val ∈ A₀(χ) ∧ x = mkΘ(χ, f) := by
  let D : Submodule ℂ P := (A₀(χ)).comap (P).subtype
  let q : P →ₗ[ℂ] Θ₀(χ) := (Π(χ)).mkQ
  have hEq : archNuclearityDenominator χ = D.map q := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro _ ⟨f, hf, rfl⟩
      exact Submodule.subset_span ⟨f, hf, rfl⟩
  rw [hEq]
  exact exists_congr fun f ↦ and_congr_right fun _ ↦ eq_comm

private theorem archNuclearity_flatTests_mono {Q R : Prop} (h : Q → R) :
    globalArchimedeanFlatTests F R ≤ globalArchimedeanFlatTests F Q := by
  apply Submodule.span_mono
  rintro _ ⟨a, b, f, hf, hR, rfl⟩
  exact ⟨a, b, f, hf, hR ∘ h, rfl⟩

/-- Reduction to additive moment factorization and the vanishing of weighted finite
coinvariants modulo the restricted flat space and the theta kernel. -/
private theorem archNuclearity_of_finiteMassReduction
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (x : Θ₀(χ))
    (H : ω(χ) = 1 → ∃ (i : ArchTests →ₗ[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (b₀ : FiniteTests),
      j b₀ = 1 ∧
      (∀ a b, hatL (tensor (a ⊗ₜ[ℂ] b)) = i a * j b) ∧
      (∀ (a : ArchTests) (h : Flat), (∀ z, a (Multiplicative.ofAdd z) = h.val (coord z)) →
        (i a = 0 ↔ (∫ y : Coord, h.val y) = 0)) ∧
      (∀ a ∈ Aflat, ∀ b, j b = 0 → tensor (a ⊗ₜ[ℂ] b) ∈ A₀(χ) ⊔ K(χ))) :
    x ∈ archNuclearityDenominator χ ↔
      ∃ f : P, f.val ∈ A ∧ x = mkΘ(χ, f) := by
  rw [archNuclearityDenominator_mem_restricted]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, archNuclearity_flatTests_mono (False.elim : False → ω(χ) = 1) hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    by_cases hω : ω(χ) = 1
    swap
    · exact ⟨f, archNuclearity_flatTests_mono hω hf, rfl⟩
    obtain ⟨i, j, b₀, hb, hL, hi, hK⟩ := H hω
    have hA (a : ArchTests) (ha : a ∈ Aflat) (h0 : i a = 0) (b : FiniteTests) :
        tensor (a ⊗ₜ[ℂ] b) ∈ A₀(χ) := by
      obtain ⟨h, hh⟩ := ha
      exact Submodule.subset_span ⟨a, b, h, hh, fun _ ↦ (hi a h hh).mp h0, rfl⟩
    have hspan : A ≤ Submodule.span ℂ {v | ∃ a ∈ Aflat, ∃ b, tensor (a ⊗ₜ[ℂ] b) = v} := by
      apply Submodule.span_mono
      rintro _ ⟨a, b, h, hh, _, rfl⟩
      exact ⟨a, ⟨h, hh⟩, b, rfl⟩
    have hsum := tensor_mem_flat_moment_sup (tensor).toLinearMap Aflat (A₀(χ)) (K(χ)) i j hatL b₀
      hb hL hA hK (hspan hf) ((mem_adelePolarSubspace f.val).mp f.property).2
    obtain ⟨g, hg, k, hk, hgf⟩ := Submodule.mem_sup.mp hsum
    have hg0 : g ∈ P := by
      have hgflat : g ∈ A := archNuclearity_flatTests_mono (False.elim : False → ω(χ) = 1) hg
      apply (globalArchimedeanFlatTests_zero_moments g hgflat).2.mpr
      suffices hatL g = 0 from this
      refine Submodule.span_induction (p := fun y _ ↦ hatL y = 0) ?_ ?_ ?_ ?_ hg
      · rintro _ ⟨a, b, h, hh, hM, rfl⟩
        exact (hL a b).trans (mul_eq_zero_of_left ((hi a h hh).mpr (hM hω)) _)
      · exact map_zero _
      · intro a b _ _ ha hb'
        rw [map_add, ha, hb', add_zero]
      · intro c y _ hy
        rw [map_smul, hy, smul_zero]
    refine ⟨⟨g, hg0⟩, hg, (Submodule.Quotient.eq (Π(χ))).mpr ?_⟩
    change f.val - g ∈ K(χ)
    have he : f.val - g = k := by rw [← hgf, add_comm g k, add_sub_cancel_right]
    rwa [he]

open scoped RestrictedProduct
local notation "AF" => FiniteAdeleRing (𝓞 F) F
/-- In mixed archimedean coordinates the global Fourier value at zero factors
as ordinary archimedean volume integration against a fixed finite functional. -/
private theorem archNuclearity_productMoment :
    ∃ J : FiniteTests → ℂ, ∀ (a : ℬ(InfiniteAdeleRing F)) (b : FiniteTests),
      adeleSchwartzFourier (F := F) (tensor (a ⊗ₜ[ℂ] b)) (Multiplicative.ofAdd 0) =
        (∫ y : Coord, a (Multiplicative.ofAdd ((coord).symm y))) * J b := by
  let (v : V) : CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicCompletionIntegers v
  let (v : V) : LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
  let : Fact (∀ v : V, IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace AF := inferInstanceAs
    (LocallyCompactSpace (Πʳ v : V, [v.adicCompletion F, v.adicCompletionIntegers F]))
  let : LocallyCompactSpace 𝔸[F] := inferInstanceAs
    (LocallyCompactSpace (InfiniteAdeleRing F × AF))
  let := ratAdele_secondCountable
  obtain ⟨e, _, _⟩ := exists_adeleTrace_dualCoordinates F
  let : SecondCountableTopology 𝔸[F] := e.symm.toHomeomorph.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (InfiniteAdeleRing F × AF) := inferInstanceAs (SecondCountableTopology 𝔸[F])
  let : SecondCountableTopology AF :=
    (isEmbedding_prodMkRight (X := InfiniteAdeleRing F) (Y := AF) 0).secondCountableTopology
  let : IsTopologicalAddGroup AF := inferInstanceAs
    (IsTopologicalAddGroup (Πʳ v : V, [v.adicCompletion F, v.adicCompletionIntegers F]))
  let : IsTopologicalAddGroup 𝔸[F] := inferInstanceAs
    (IsTopologicalAddGroup (InfiniteAdeleRing F × AF))
  let : MeasurableSpace AF := borel _
  let : BorelSpace AF := ⟨rfl⟩
  let : MeasurableSpace 𝔸[F] := borel _
  let : BorelSpace 𝔸[F] := ⟨rfl⟩
  let d : (Coord × AF) ≃ₜ+ 𝔸[F] :=
    { toAddEquiv := (coord).symm.toAddEquiv.prodCongr (AddEquiv.refl _)
      continuous_toFun := ((continuous_infiniteAdeleRingEquivMixedSpace_symm F).comp continuous_fst).prodMk
        continuous_snd
      continuous_invFun := ((continuous_infiniteAdeleRingEquivMixedSpace F).comp continuous_fst).prodMk
        continuous_snd }
  let μf := Measure.addHaar (G := AF)
  let μ : Measure (Coord × AF) := (volume : Measure Coord).prod μf
  let : μ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let ν : Measure 𝔸[F] := μ.map d
  let : ν.IsAddHaarMeasure := d.isAddHaarMeasure_map μ
  let m := additiveTamagawaMeasure F
  let : m.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let c := m.addHaarScalarFactor ν
  have hc : m = c • ν := Measure.isAddLeftInvariant_eq_smul m ν
  refine ⟨fun b ↦ (c : ℂ) * ∫ x, b (Multiplicative.ofAdd x) ∂μf, fun a b ↦ ?_⟩
  rw [(adeleSchwartzFourier_apply_zero _).2]
  change (∫ x : 𝔸[F], tensor (a ⊗ₜ[ℂ] b) (Multiplicative.ofAdd x) ∂m) = _
  rw [hc, integral_smul_nnreal_measure]
  change (c : ℂ) * ∫ x : 𝔸[F], tensor (a ⊗ₜ[ℂ] b) (Multiplicative.ofAdd x) ∂ν = _
  rw [show ν = μ.map d.toHomeomorph.toMeasurableEquiv from rfl, integral_map_equiv]
  have h (x : Coord × AF) :
      tensor (a ⊗ₜ[ℂ] b) (Multiplicative.ofAdd (d.toHomeomorph.toMeasurableEquiv x)) =
        a (Multiplicative.ofAdd ((coord).symm x.1)) * b (Multiplicative.ofAdd x.2) :=
    (adeleSchwartz_inductiveTensor_equiv F).choose_spec a b (d x)
  simp_rw [h]
  exact (congrArg ((c : ℂ) * ·) (integral_prod_mul (μ := (volume : Measure Coord)) (ν := μf)
    (fun y ↦ a (Multiplicative.ofAdd ((coord).symm y))) (fun y ↦ b (Multiplicative.ofAdd y)))).trans
      (mul_left_comm _ _ _)

local notation "hatC" => (ContinuousLinearMap.snd ℂ ℂ ℂ).comp
  (⟨(adelePolarValues_isLinear (F := F)).mk' adelePolarValues,
    adelePolarValues_continuous⟩ : ℬ(𝔸[F]) →L[ℂ] ℂ × ℂ)

private theorem archNuclearity_nonzero_pure_moment :
    ∃ (a : ArchTests) (b : FiniteTests), hatC (tensor (a ⊗ₜ[ℂ] b)) ≠ 0 := by
  by_contra! h
  have hz : (hatC).toLinearMap.comp (tensor).toLinearMap = 0 :=
    TensorProduct.ext' fun a b ↦ h a b
  obtain ⟨f, hf⟩ := adelePolarValues_surjective (F := F) ((0, 1) : ℂ × ℂ)
  have hf' : hatC f = 1 := congrArg Prod.snd hf
  have ht := LinearMap.congr_fun hz ((tensor).symm f)
  change hatC (tensor ((tensor).symm f)) = 0 at ht
  rw [(tensor).apply_symm_apply, hf'] at ht
  exact one_ne_zero ht

private theorem archNuclearity_normalized_moment :
    ∃ (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (a₀ : ArchTests) (b₀ : FiniteTests),
      i a₀ ≠ 0 ∧ j b₀ = 1 ∧
      (∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b) ∧
      (∀ (a : ArchTests) (h : Flat), (∀ z, a (Multiplicative.ofAdd z) = h.val (coord z)) →
        (i a = 0 ↔ (∫ y : Coord, h.val y) = 0)) := by
  obtain ⟨a₀, b₀, hab₀⟩ := archNuclearity_nonzero_pure_moment (F := F)
  obtain ⟨rawJ, hraw⟩ := archNuclearity_productMoment (F := F)
  let rawI (a : ArchTests) := ∫ y : Coord, a (Multiplicative.ofAdd ((coord).symm y))
  have hL (a : ArchTests) (b : FiniteTests) : hatC (tensor (a ⊗ₜ[ℂ] b)) = rawI a * rawJ b := hraw a b
  have hj₀ : rawJ b₀ ≠ 0 := right_ne_zero_of_mul (fun hz ↦ hab₀ ((hL a₀ b₀).trans hz))
  have hi₀ : rawI a₀ ≠ 0 := left_ne_zero_of_mul (fun hz ↦ hab₀ ((hL a₀ b₀).trans hz))
  let T := InductiveTensor ArchTests FiniteTests
  let eb : ArchTests →ₗ[ℂ] T := (TensorProduct.mk ℂ ArchTests FiniteTests).flip b₀
  have heb : Continuous eb := by
    let h := withGeneratingSeminorms_spec (ArchTests ⊗[ℂ] FiniteTests)
      (fun p : {p : Seminorm ℂ (ArchTests ⊗[ℂ] FiniteTests) //
        (∀ a : ArchTests, Continuous (fun b : FiniteTests ↦ p (a ⊗ₜ[ℂ] b))) ∧
        (∀ b : FiniteTests, Continuous (fun a : ArchTests ↦ p (a ⊗ₜ[ℂ] b)))} ↦ p.val)
    exact h.continuous_of_continuous_comp eb fun p ↦ p.property.2 b₀
  let i : ArchTests →L[ℂ] ℂ := (hatC).comp ((tensor).toContinuousLinearMap.comp ⟨eb, heb⟩)
  let j : FiniteTests →ₗ[ℂ] ℂ := (hatC (tensor (a₀ ⊗ₜ[ℂ] b₀)))⁻¹ •
    ((hatC).toLinearMap.comp ((tensor).toLinearMap.comp (TensorProduct.mk ℂ ArchTests FiniteTests a₀)))
  have hi (a : ArchTests) : i a = rawI a * rawJ b₀ := hL a b₀
  have hj (b : FiniteTests) : j b = (rawI a₀ * rawJ b₀)⁻¹ * (rawI a₀ * rawJ b) := by
    change (hatC (tensor (a₀ ⊗ₜ[ℂ] b₀)))⁻¹ * hatC (tensor (a₀ ⊗ₜ[ℂ] b)) = _
    rw [hL, hL]
  refine ⟨i, j, a₀, b₀, hab₀, ?_, ?_, ?_⟩
  · rw [hj, inv_mul_cancel₀ (mul_ne_zero hi₀ hj₀)]
  · intro a b
    rw [hL, hi, hj]
    field_simp
  · intro a h hh
    rw [hi, mul_eq_zero, or_iff_left hj₀]
    have hh' (y : Coord) : a (Multiplicative.ofAdd ((coord).symm y)) = h.val y := by
      rw [hh, RingEquiv.apply_symm_apply]
    have hI : rawI a = ∫ y : Coord, h.val y :=
      congrArg (fun f : Coord → ℂ ↦ ∫ y, f y) (funext hh')
    rw [hI]

local notation "A∞" => InfiniteAdeleRing F
local notation "𝕀" => IdeleGroup (𝓞 F) F

private def archNuclearity_archUnit (u : A∞ˣ) : 𝕀 where
  val := (u.val, 1)
  inv := (u.inv, 1)
  val_inv := Prod.ext u.val_inv (one_mul 1)
  inv_val := Prod.ext u.inv_val (one_mul 1)

private def archNuclearity_finiteUnit (u : AFˣ) : 𝕀 where
  val := (1, u.val)
  inv := (1, u.inv)
  val_inv := Prod.ext (one_mul 1) u.val_inv
  inv_val := Prod.ext (one_mul 1) u.inv_val

private def archNuclearity_translateLinear {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (u : Rˣ) : ℬ(R) →ₗ[ℂ] ℬ(R) where
  toFun := schwartzBruhatUnitTranslate u
  map_add' := fun _ _ ↦ Subtype.ext rfl
  map_smul' := fun _ _ ↦ Subtype.ext rfl

private theorem archNuclearity_translate_pure (u : A∞ˣ) (v : AFˣ) (a : ArchTests) (b : FiniteTests) :
    schwartzBruhatUnitTranslate (archNuclearity_archUnit u * archNuclearity_finiteUnit v)
      (tensor (a ⊗ₜ[ℂ] b)) =
    tensor (schwartzBruhatUnitTranslate u a ⊗ₜ[ℂ] schwartzBruhatUnitTranslate v b) := by
  apply Subtype.ext
  funext x
  change schwartzBruhatUnitTranslate (archNuclearity_archUnit u * archNuclearity_finiteUnit v)
      (tensor (a ⊗ₜ[ℂ] b)) (Multiplicative.ofAdd x.toAdd) =
    tensor (schwartzBruhatUnitTranslate u a ⊗ₜ[ℂ] schwartzBruhatUnitTranslate v b)
      (Multiplicative.ofAdd x.toAdd)
  rw [schwartzBruhatUnitTranslate_apply,
    (adeleSchwartz_inductiveTensor_equiv F).choose_spec,
    (adeleSchwartz_inductiveTensor_equiv F).choose_spec,
    schwartzBruhatUnitTranslate_apply, schwartzBruhatUnitTranslate_apply]
  change a (Multiplicative.ofAdd ((1 * (↑u⁻¹ : A∞)) * x.toAdd.1)) *
    b (Multiplicative.ofAdd (((↑v⁻¹ : AF) * 1) * x.toAdd.2)) = _
  rw [mul_one, one_mul]

private theorem archNuclearity_translate_one {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (a : ℬ(R)) : schwartzBruhatUnitTranslate 1 a = a := by
  apply Subtype.ext
  funext x
  change schwartzBruhatUnitTranslate 1 a (Multiplicative.ofAdd x.toAdd) = _
  rw [schwartzBruhatUnitTranslate_apply, inv_one, Units.val_one, one_mul]
  rfl

private theorem archNuclearity_unit_arch_finite (w : 𝕀) :
    ∃ u : A∞ˣ, ∃ v : AFˣ, w = archNuclearity_archUnit u * archNuclearity_finiteUnit v := by
  refine ⟨Units.map (RingHom.fst A∞ AF).toMonoidHom w,
    Units.map (RingHom.snd A∞ AF).toMonoidHom w, ?_⟩
  apply Units.ext
  exact Prod.ext (mul_one _).symm (one_mul _).symm

local notation "absValue(" u ")" => ((((ideleNorm F u).val : ℝ) : ℂ))

private theorem archNuclearity_hatC_translate (u : 𝕀) (f : ℬ(𝔸[F])) :
    hatC (schwartzBruhatUnitTranslate u f) = absValue(u) * hatC f := by
  have h := globalThetaPolarValues_snd_translate (QuotientGroup.mk u) (Submodule.Quotient.mk f)
  rw [(existsUnique_globalThetaAction (F := F)).exists.choose_spec.2 u f] at h
  exact h

private theorem archNuclearity_moment_arch_translate (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ)
    (b₀ : FiniteTests) (hb : j b₀ = 1) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (u : A∞ˣ) (a : ArchTests) :
    i (schwartzBruhatUnitTranslate u a) = absValue(archNuclearity_archUnit u) * i a := by
  have h := archNuclearity_hatC_translate
    (archNuclearity_archUnit u * archNuclearity_finiteUnit (F := F) 1) (tensor (a ⊗ₜ[ℂ] b₀))
  rw [archNuclearity_translate_pure, archNuclearity_translate_one, hL, hL, hb, mul_one, mul_one,
    show archNuclearity_finiteUnit (F := F) 1 = 1 from Units.ext rfl, mul_one] at h
  exact h

private theorem archNuclearity_moment_finite_translate (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ)
    (a₀ : ArchTests) (ha : i a₀ ≠ 0) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (v : AFˣ) (b : FiniteTests) :
    j (schwartzBruhatUnitTranslate v b) = absValue(archNuclearity_finiteUnit v) * j b := by
  have h := archNuclearity_hatC_translate
    (archNuclearity_archUnit (F := F) 1 * archNuclearity_finiteUnit v) (tensor (a₀ ⊗ₜ[ℂ] b))
  rw [archNuclearity_translate_pure, archNuclearity_translate_one, hL, hL,
    show archNuclearity_archUnit (F := F) 1 = 1 from Units.ext rfl, one_mul,
    mul_left_comm] at h
  exact mul_left_cancel₀ ha h

private theorem archNuclearity_translate_mul (u v : 𝕀) (f : ℬ(𝔸[F])) :
    schwartzBruhatUnitTranslate u (schwartzBruhatUnitTranslate v f) =
    schwartzBruhatUnitTranslate (u * v) f := by
  apply Subtype.ext
  funext x
  change f (Multiplicative.ofAdd (v.inv * (u.inv * x.toAdd))) =
    f (Multiplicative.ofAdd ((u * v).inv * x.toAdd))
  exact congrArg (fun y ↦ f (Multiplicative.ofAdd y)) (mul_assoc v.inv u.inv x.toAdd).symm

private theorem archNuclearity_archLift (v : AFˣ) :
    ∃ u : A∞ˣ, ideleNorm F (archNuclearity_archUnit u) = ideleNorm F (archNuclearity_finiteUnit v) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let t := ideleNorm F (archNuclearity_finiteUnit v)
  let g := singlePlaceIdeleNormSection F w t
  let u := Units.map (RingHom.fst A∞ AF).toMonoidHom g
  have hu : archNuclearity_archUnit u = g := Units.ext (Prod.ext rfl rfl)
  exact ⟨u, hu ▸ singlePlaceIdeleNormSection_rightInverse F w t⟩

private theorem archNuclearity_theta_translate_sameNorm
    (χ : PontryaginDual C𝔽) (hω : ω(χ) = 1) (u v : 𝕀) (h : ideleNorm F u = ideleNorm F v)
    (f : ℬ(𝔸[F])) :
    homogeneousAdelicThetaLinearMap F (ω(χ)) (schwartzBruhatUnitTranslate u f) =
    homogeneousAdelicThetaLinearMap F (ω(χ)) (schwartzBruhatUnitTranslate v f) := by
  let g := u * v⁻¹
  have hg : ideleNorm F g = 1 := by
    change ideleNorm F (u * v⁻¹) = _
    rw [map_mul, map_inv, h, mul_inv_cancel]
  let k : (ideleClassNorm F).ker :=
    ⟨QuotientGroup.mk g, MonoidHom.mem_ker.mpr (show ideleNorm F g = 1 from hg)⟩
  have he := globalConverse_nontrivial_exact_theta_translate (ω(χ)) k g rfl
    (schwartzBruhatUnitTranslate v f)
  have hw : (ω(χ) k : ℂ) = 1 :=
    (congrArg (fun χ' : PontryaginDual (ideleClassNorm F).ker ↦ (χ' k : ℂ)) hω).trans rfl
  let M := homogeneousAdelicThetaLinearMap F (ω(χ))
  have htrans : schwartzBruhatUnitTranslate g (schwartzBruhatUnitTranslate v f) =
      schwartzBruhatUnitTranslate u f :=
    (archNuclearity_translate_mul g v f).trans
      (congrArg (fun s : 𝕀 ↦ schwartzBruhatUnitTranslate s f) (inv_mul_cancel_right u v))
  exact ((congrArg M htrans).symm.trans he).trans
    ((congrArg (fun c : ℂ ↦ c • M (schwartzBruhatUnitTranslate v f)) hw).trans (one_smul _ _))

/-- A finite eigendistribution of additive weight extends by tensoring with the
archimedean moment. Global rank one then determines it uniquely. -/
private theorem archNuclearity_finiteEigen_unique
    (hcont : ∀ L : FiniteTests →ₗ[ℂ] ℂ, Continuous L)
    (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (a₀ : ArchTests) (b₀ : FiniteTests)
    (ha : i a₀ ≠ 0) (hb : j b₀ = 1) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (L : FiniteTests →ₗ[ℂ] ℂ)
    (hLcov : ∀ (u : AFˣ) b, L (schwartzBruhatUnitTranslate u b) = absValue(archNuclearity_finiteUnit u) * L b) :
    ∃ c : ℂ, L = c • j := by
  let T := InductiveTensor ArchTests FiniteTests
  let Q : T →ₗ[ℂ] ℂ := (LinearMap.mul' ℂ ℂ).comp (TensorProduct.map i.toLinearMap L)
  have hQ (a : ArchTests) (b : FiniteTests) : Q (a ⊗ₜ[ℂ] b) = i a * L b := by
    change (LinearMap.mul' ℂ ℂ) (TensorProduct.map i.toLinearMap L (a ⊗ₜ[ℂ] b)) = _
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  have hcQ : Continuous Q := by
    let hS := withGeneratingSeminorms_spec (ArchTests ⊗[ℂ] FiniteTests)
      (fun p : {p : Seminorm ℂ (ArchTests ⊗[ℂ] FiniteTests) //
        (∀ a : ArchTests, Continuous (fun b : FiniteTests ↦ p (a ⊗ₜ[ℂ] b))) ∧
        (∀ b : FiniteTests, Continuous (fun a : ArchTests ↦ p (a ⊗ₜ[ℂ] b)))} ↦ p.val)
    refine (PolynormableSpace.withSeminorms ℂ ℂ).continuous_of_continuous_comp Q fun q ↦ ?_
    refine hS.continuous_seminorm ⟨q.val.comp Q, fun a ↦ q.property.comp ?_, fun b ↦ q.property.comp ?_⟩
    · exact (continuous_const.mul (hcont L)).congr fun b ↦ (hQ a b).symm
    · exact (i.continuous.mul continuous_const).congr fun a ↦ (hQ a b).symm
  let D : StrongDual ℂ ℬ(𝔸[F]) := (⟨Q, hcQ⟩ : T →L[ℂ] ℂ).comp (tensor).symm.toContinuousLinearMap
  have hD (a : ArchTests) (b : FiniteTests) : D (tensor (a ⊗ₜ[ℂ] b)) = i a * L b :=
    (congrArg Q ((tensor).symm_apply_apply (a ⊗ₜ[ℂ] b))).trans (hQ a b)
  let c := ideleClassNormTwist (1 : U) 1
  have hDcov (w : 𝕀) (f : ℬ(𝔸[F])) :
      D (schwartzBruhatUnitTranslate w f) = absValue(w) * D f := by
    obtain ⟨u, v, rfl⟩ := archNuclearity_unit_arch_finite w
    let w := archNuclearity_archUnit u * archNuclearity_finiteUnit v
    let L₁ := (D.toLinearMap.comp (archNuclearity_translateLinear w)).comp (tensor).toLinearMap
    let L₂ := absValue(w) • D.toLinearMap.comp (tensor).toLinearMap
    have he : L₁ = L₂ := by
      refine TensorProduct.ext' fun a b ↦ ?_
      change D (schwartzBruhatUnitTranslate (archNuclearity_archUnit u * archNuclearity_finiteUnit v)
        (tensor (a ⊗ₜ[ℂ] b))) = absValue(archNuclearity_archUnit u * archNuclearity_finiteUnit v) *
          D (tensor (a ⊗ₜ[ℂ] b))
      rw [archNuclearity_translate_pure, hD, hD, archNuclearity_moment_arch_translate i j b₀ hb hL,
        hLcov, map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_mul_mul_comm]
    obtain ⟨x, rfl⟩ := (tensor).surjective f
    exact LinearMap.congr_fun he x
  have hmem : D ∈ adelicEigendistributions c := by
    intro w f
    change _ = ((1 : ℂ) * absValue(w) ^ (1 : ℂ)) * D f
    rw [Complex.cpow_one, one_mul]
    exact hDcov w f
  let H : StrongDual ℂ ℬ(𝔸[F]) := hatC
  have hH : H ∈ adelicEigendistributions c := by
    intro w f
    change _ = ((1 : ℂ) * absValue(w) ^ (1 : ℂ)) * H f
    rw [Complex.cpow_one, one_mul]
    exact archNuclearity_hatC_translate w f
  have hnH : H ≠ 0 := by
    intro he
    have hh := hL a₀ b₀
    change H (tensor (a₀ ⊗ₜ[ℂ] b₀)) = _ at hh
    rw [he, zero_apply, hb, mul_one] at hh
    exact ha hh.symm
  have hr := Module.rank_eq_one_iff_finrank_eq_one.mp (adelicEigendistributions_rank c)
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hr hH hnH, Submodule.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, LinearMap.ext fun b ↦ ?_⟩
  have he := congrArg (fun d : StrongDual ℂ ℬ(𝔸[F]) ↦ d (tensor (a₀ ⊗ₜ[ℂ] b))) hz
  change z * hatC (tensor (a₀ ⊗ₜ[ℂ] b)) = D (tensor (a₀ ⊗ₜ[ℂ] b)) at he
  rw [hL, hD, mul_left_comm] at he
  exact (mul_left_cancel₀ ha he).symm

/-- If the additive-mass functional spans the algebraic eigenfunctionals,
the weighted translation differences generate its kernel. -/
private theorem span_weightedDifferences_eq_ker
    {W G : Type*} [AddCommGroup W] [Module ℂ W] (T : G → W → W) (c : G → ℂ)
    (J : W →ₗ[ℂ] ℂ) (hJ : ∀ u w, J (T u w) = c u * J w)
    (huniq : ∀ L : W →ₗ[ℂ] ℂ, (∀ u w, L (T u w) = c u * L w) → ∃ z : ℂ, L = z • J) :
    Submodule.span ℂ {x | ∃ u w, x = T u w - c u • w} = J.ker := by
  let D := Submodule.span ℂ {x | ∃ u w, x = T u w - c u • w}
  have hD : D ≤ J.ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, w, rfl⟩
    change J (T u w - c u • w) = 0
    rw [map_sub, map_smul, smul_eq_mul, hJ, sub_self]
  apply Subspace.dualAnnihilator_inj.mp
  apply le_antisymm
  · intro l hl
    have hL (u : G) (w : W) : l (T u w) = c u * l w := by
      have hm : T u w - c u • w ∈ D := Submodule.subset_span ⟨u, w, rfl⟩
      have hz := (D.mem_dualAnnihilator l).mp hl _ hm
      rw [map_sub, map_smul, smul_eq_mul] at hz
      exact sub_eq_zero.mp hz
    obtain ⟨z, rfl⟩ := huniq l hL
    exact (J.ker.mem_dualAnnihilator _).mpr fun w hw ↦ by
      change z * J w = 0
      rw [LinearMap.mem_ker.mp hw, mul_zero]
  · intro l hl
    exact (D.mem_dualAnnihilator _).mpr fun w hw ↦ (J.ker.mem_dualAnnihilator _).mp hl _ (hD hw)


private theorem archNuclearity_weightedDifference
    (χ : PontryaginDual C𝔽) (hω : ω(χ) = 1)
    (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (b₀ : FiniteTests)
    (hb₀ : j b₀ = 1) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (hi : ∀ (a : ArchTests) (h : Flat), (∀ z, a (Multiplicative.ofAdd z) = h.val (coord z)) →
      (i a = 0 ↔ (∫ y : Coord, h.val y) = 0))
    (a : ArchTests) (ha : a ∈ Aflat) (b : FiniteTests) (v : AFˣ) :
    tensor (a ⊗ₜ[ℂ] (schwartzBruhatUnitTranslate v b - absValue(archNuclearity_finiteUnit v) • b)) ∈
      A₀(χ) ⊔ K(χ) := by
  obtain ⟨u, hu⟩ := archNuclearity_archLift v
  let c := absValue(archNuclearity_finiteUnit v)
  let a' := schwartzBruhatUnitTranslate u a - c • a
  have ha' : a' ∈ Aflat :=
    Submodule.sub_mem _ (archNuclearity_flatFactors_translate u a ha) (Submodule.smul_mem _ _ ha)
  have hia : i a' = 0 := by
    change i (schwartzBruhatUnitTranslate u a - c • a) = 0
    rw [map_sub, map_smul, archNuclearity_moment_arch_translate i j b₀ hb₀ hL, hu, smul_eq_mul, sub_self]
  let p := tensor (a' ⊗ₜ[ℂ] b)
  have hp : p ∈ A₀(χ) := by
    obtain ⟨h, hh⟩ := ha'
    exact Submodule.subset_span ⟨a', b, h, hh, fun _ ↦ (hi a' h hh).mp hia, rfl⟩
  let q := tensor (a ⊗ₜ[ℂ] (schwartzBruhatUnitTranslate v b - c • b))
  have hq : q - p ∈ K(χ) := by
    let M := homogeneousAdelicThetaLinearMap F (ω(χ))
    have htheta := archNuclearity_theta_translate_sameNorm χ hω
      (archNuclearity_finiteUnit v) (archNuclearity_archUnit u) hu.symm
      (tensor (a ⊗ₜ[ℂ] b))
    have htF := archNuclearity_translate_pure (1 : A∞ˣ) v a b
    have htA := archNuclearity_translate_pure u (1 : AFˣ) a b
    rw [archNuclearity_translate_one, show archNuclearity_archUnit (F := F) 1 = 1 from Units.ext rfl,
      one_mul] at htF
    rw [archNuclearity_translate_one, show archNuclearity_finiteUnit (F := F) 1 = 1 from Units.ext rfl,
      mul_one] at htA
    let H := M.comp (tensor).toLinearMap
    have he : H (a ⊗ₜ[ℂ] schwartzBruhatUnitTranslate v b) =
        H (schwartzBruhatUnitTranslate u a ⊗ₜ[ℂ] b) :=
      ((congrArg M htF).symm.trans htheta).trans (congrArg M htA)
    have heq : M q = M p := by
      change H (a ⊗ₜ[ℂ] (schwartzBruhatUnitTranslate v b - c • b)) =
        H ((schwartzBruhatUnitTranslate u a - c • a) ⊗ₜ[ℂ] b)
      rw [TensorProduct.tmul_sub, TensorProduct.sub_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      exact (map_sub H _ _).trans ((congrArg (· - H ((c • a) ⊗ₜ[ℂ] b)) he).trans
        (map_sub H _ _).symm)
    exact (map_sub M q p).trans (sub_eq_zero.mpr heq)
  refine Submodule.mem_sup.mpr ⟨p, hp, q - p, hq, ?_⟩
  change p + (q - p) = q
  rw [add_comm, sub_add_cancel]

private theorem archNuclearity_discard_massZero
    (χ : PontryaginDual C𝔽) (hω : ω(χ) = 1)
    (hcont : ∀ L : FiniteTests →ₗ[ℂ] ℂ, Continuous L)
    (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (a₀ : ArchTests) (b₀ : FiniteTests)
    (ha₀ : i a₀ ≠ 0) (hb₀ : j b₀ = 1) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (hi : ∀ (a : ArchTests) (h : Flat), (∀ z, a (Multiplicative.ofAdd z) = h.val (coord z)) →
      (i a = 0 ↔ (∫ y : Coord, h.val y) = 0))
    (a : ArchTests) (ha : a ∈ Aflat) (b : FiniteTests) (hb : j b = 0) :
    tensor (a ⊗ₜ[ℂ] b) ∈ A₀(χ) ⊔ K(χ) := by
  let wt := fun v : AFˣ ↦ absValue(archNuclearity_finiteUnit v)
  have heq := span_weightedDifferences_eq_ker (schwartzBruhatUnitTranslate (R := AF)) wt j
    (archNuclearity_moment_finite_translate i j a₀ ha₀ hL)
    (archNuclearity_finiteEigen_unique hcont i j a₀ b₀ ha₀ hb₀ hL)
  let M : FiniteTests →ₗ[ℂ] ℬ(𝔸[F]) := (tensor).toLinearMap.comp (TensorProduct.mk ℂ ArchTests FiniteTests a)
  have H : Submodule.span ℂ {x | ∃ u w, x = schwartzBruhatUnitTranslate u w - wt u • w} ≤
      (A₀(χ) ⊔ K(χ)).comap M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, w, rfl⟩
    exact archNuclearity_weightedDifference χ hω i j b₀ hb₀ hL hi a ha w u
  exact (heq ▸ H) hb

/-- Transport the finest topology of the empty tail without changing the
representation of the finite adelic test functions. -/
private theorem archNuclearity_finiteFunctionals_continuous (L : FiniteTests →ₗ[ℂ] ℂ) :
    Continuous L := by
  obtain ⟨e, he, _⟩ := finiteAdeleTail_empty F
  let : Fact (∀ w : {w : V // w ∉ (∅ : Finset V)},
      IsOpen (w.val.adicCompletionIntegers F : Set (w.val.adicCompletion F))) :=
    ⟨fun w ↦ Valued.isOpen_valuationSubring (w.val.adicCompletion F)⟩
  let : IsTopologicalRing (FiniteAdeleTail F ∅) := RestrictedProduct.isTopologicalRing _
  let : IsTopologicalGroup (Multiplicative (FiniteAdeleTail F ∅)) := inferInstance
  let d : Multiplicative (FiniteAdeleTail F ∅) ≃ₜ* Multiplicative AF :=
    ⟨e.toAddEquiv.toMultiplicative, he.continuous, he.homeomorph.symm.continuous.congr
      fun x ↦ e.injective (he.homeomorph.apply_symm_apply x |>.trans (e.apply_symm_apply x).symm)⟩
  let (v : V) : CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicCompletionIntegers v
  let (v : V) : LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
  let : Fact (∀ v : V, IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let : T2Space (Multiplicative AF) := inferInstanceAs
    (T2Space (Πʳ w : V, [w.adicCompletion F, w.adicCompletionIntegers F]))
  let : LocallyCompactSpace (Multiplicative AF) := inferInstanceAs
    (LocallyCompactSpace (Πʳ w : V, [w.adicCompletion F, w.adicCompletionIntegers F]))
  let : T2Space (Multiplicative (FiniteAdeleTail F ∅)) := d.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (FiniteAdeleTail F ∅)) :=
    d.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  obtain ⟨T, hT⟩ := schwartzBruhat_transport d
  obtain ⟨S, hS⟩ := schwartzBruhat_transport d.symm
  let W := ℬ(FiniteAdeleTail F ∅)
  let Q : W →ₗ[ℂ] ℂ := L.comp T.toLinearMap
  have ht := (finiteProduct_tailSchwartz_finestTopology F ∅ ∅).2
  have hQ : Continuous Q :=
    Eq.mpr (congrArg (fun t : TopologicalSpace W ↦ @Continuous W ℂ t _ Q) ht)
      (continuous_of_finestLocallyConvex W Q)
  have hinv (f : FiniteTests) : T (S f) = f := by
    apply Subtype.ext
    funext x
    change T (S f) x = f x
    rw [hT, hS, ContinuousMulEquiv.symm_symm, d.apply_symm_apply]
  exact (hQ.comp S.continuous).congr fun f ↦ congrArg L (hinv f)

/-- Paper: Equations (7.4.3.1) and (7.4.3.12), pp. 368 and 371.
In the homogeneous theta image the factorwise moment condition agrees with
imposing the two global polar conditions on the unrestricted flat tensors. -/
theorem mem_archNuclearityDenominator_iff_flatPolarImage (x : Θ₀(χ)) :
    x ∈ archNuclearityDenominator χ ↔
      ∃ f : P, f.val ∈ globalArchimedeanFlatTests F ∧ x = mkΘ(χ, f) := by
  refine archNuclearity_of_finiteMassReduction χ x fun hω ↦ ?_
  obtain ⟨i, j, a₀, b₀, ha₀, hb₀, hL, hi⟩ := archNuclearity_normalized_moment (F := F)
  exact ⟨i.toLinearMap, j, b₀, hb₀, hL, hi,
    archNuclearity_discard_massZero χ hω archNuclearity_finiteFunctionals_continuous
      i j a₀ b₀ ha₀ hb₀ hL hi⟩

end FlatPolarImage

/-- Paper: Equation (7.4.3.13), p. 372.
The archimedean orbital quotient divides the zero-moment theta space by its flat image.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its definition (#5398). -/
def ArchNuclearityQuotient := Θ₀(χ) ⧸ archNuclearityDenominator χ

namespace ArchNuclearityQuotient

instance instAddCommGroup : AddCommGroup (ArchNuclearityQuotient χ) :=
  inferInstanceAs (AddCommGroup (Θ₀(χ) ⧸ archNuclearityDenominator χ))

instance instModule : Module ℂ (ArchNuclearityQuotient χ) :=
  inferInstanceAs (Module ℂ (Θ₀(χ) ⧸ archNuclearityDenominator χ))

instance instTopologicalSpace : TopologicalSpace (ArchNuclearityQuotient χ) :=
  inferInstanceAs (TopologicalSpace (Θ₀(χ) ⧸ archNuclearityDenominator χ))

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (ArchNuclearityQuotient χ) :=
  inferInstanceAs (IsTopologicalAddGroup (Θ₀(χ) ⧸ archNuclearityDenominator χ))

instance instContinuousSMul : ContinuousSMul ℂ (ArchNuclearityQuotient χ) :=
  inferInstanceAs (ContinuousSMul ℂ (Θ₀(χ) ⧸ archNuclearityDenominator χ))

end ArchNuclearityQuotient

/-- Paper: Equation (7.4.3.13), p. 372.
A test represents zero in the archimedean quotient exactly when its theta class
has an archimedean-flat zero-moment representative. -/
theorem archNuclearityQuotient_mk_eq_zero (f : P) :
    (archNuclearityDenominator χ).mkQ mkΘ(χ, f) = 0 ↔
      ∃ g : P, g.val ∈ globalArchimedeanFlatTests F (ω(χ) = 1) ∧ mkΘ(χ, g) = mkΘ(χ, f) := by
  let A : Submodule ℂ P := (globalArchimedeanFlatTests F (ω(χ) = 1)).comap (P).subtype
  let q : P →ₗ[ℂ] Θ₀(χ) := (Π(χ)).mkQ
  have hle : archNuclearityDenominator χ ≤ A.map q :=
    Submodule.span_le.mpr (by
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩)
  constructor
  · intro hf
    exact hle ((Submodule.Quotient.mk_eq_zero (archNuclearityDenominator χ)).mp hf)
  · rintro ⟨g, hg, he⟩
    exact (Submodule.Quotient.mk_eq_zero (archNuclearityDenominator χ)).mpr
      (Submodule.subset_span ⟨g, hg, he.symm⟩)

-- The finite factors of (7.4.3.6) on p. 369 also carry their integer-unit
-- Tamagawa masses. A positive archimedean bump on the trivial isotype needs a
-- difference of dilates to give zero additive integral.

-- Theorem 7.4.3.1(1) (`archNuclearityDenominator_nonzero_closed`) is stated below,
-- after the jet coordinate equivalence, because its closedness half is proved from it.

local notation "gammaOrder(" χ ", " s ")" =>
  (analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s).toNat
local notation "atZeroPole(" χ ", " τ ", " hτ ")" =>
  (-(((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℝ) : ℂ) * Complex.I)

/-- Paper: Equations (7.4.3.2)–(7.4.3.3), p. 368.
In the fixed norm chart the archimedean pole set is the zero set of the reciprocal gamma
product. The pole set in that chart is discrete and closed. -/
theorem archNuclearityPoleSet_discrete :
    let S := {s : ℂ | 0 < gammaOrder(χ, s)}
    IsClosed S ∧ IsDiscrete S := by
  apply compl_mem_codiscrete_iff.mp
  have ha : AnalyticOnNhd ℂ (fun z ↦ (heckeGammaFactor χ z)⁻¹) univ :=
    fun z _ ↦ (differentiable_inv_heckeGammaFactor χ).analyticAt z
  filter_upwards [ha.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top] with z hz
  rcases hz with hz | hz <;> simp [Set.mem_compl_iff, hz]

/-- Paper: Equations (7.4.3.2)–(7.4.3.3), p. 368.
The raw order in the global chart counts the same places as the local
multiplicity of Proposition 5.3.4.5 for the restricted character. -/
theorem archNuclearityGammaOrder_eq_sLocal (S : Finset V)
    (η : PontryaginDual (SIdeleQuotient F S))
    (h : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (_hη : sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, h⟩ =
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η) (s : ℂ) :
    gammaOrder(χ, s) = sLocalArchimedeanPoleMultiplicity η s := by
  classical
  let c : ℂ → QuasiCharacter (SIdeleQuotient F S) := fun z ↦
    quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η) z
  let E : InfinitePlace F → ℂ → ℂ := fun w z ↦
    infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (c z))
  -- The chart through `η` evaluates the global twist on inserted S-ideles.
  have htwist (z : ℂ) (g : (SAdeleRing F S)ˣ) :
      c z (QuotientGroup.mk g) =
        ideleClassNormTwist χ z (QuotientGroup.mk (sIdeleInsertion F S g)) := by
    have hbase := DFunLike.congr_fun _hη (QuotientGroup.mk g)
    rw [sIdeleRestriction_mk] at hbase
    change (χ (QuotientGroup.mk (sIdeleInsertion F S g)) : ℂ) * _ ^ (0 : ℂ) =
      (η (QuotientGroup.mk g) : ℂ) at hbase
    simp only [Complex.cpow_zero, mul_one] at hbase
    change (η (QuotientGroup.mk g) : ℂ) *
        (((sIdeleQuotientNorm F S (QuotientGroup.mk g) : ℝ≥0) : ℝ) : ℂ) ^ z =
      (χ (QuotientGroup.mk (sIdeleInsertion F S g)) : ℂ) * _ ^ z
    rw [← hbase, sIdeleQuotientNorm_mk, ← ideleNorm_sIdeleInsertion]
    rfl
  have hinf (w : InfinitePlace F) (z : ℂ) : sLocalInfiniteRestriction w (c z) =
      infinitePlaceRestriction F w (ideleClassNormTwist χ z) := by
    ext1 x
    refine (htwist z _).trans ?_
    rw [sIdeleInsertion_infiniteUnit]
    rfl
  have hprod : (fun z ↦ heckeGammaFactor χ z) = ∏ w, E w := by
    funext z
    rw [Finset.prod_apply, ← prod_infiniteLocalEulerFactor_eq_heckeGammaFactor]
    simp only [E, hinf]
  -- Each local factor is a translate of a gamma factor, with entire reciprocal.
  have hEinv (w : InfinitePlace F) : Differentiable ℂ fun z ↦ (E w z)⁻¹ := by
    by_cases hw : w.IsReal
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_real η w hw
      simp only [E, c, hb]
      exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const b)
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_complex η w
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)
      simp only [E, c, hb]
      convert (Complex.differentiable_Gammaℂ_inv.comp (differentiable_id.add_const b)).const_mul
        (2 : ℂ) using 1
      funext z
      rw [inv_div, div_eq_mul_inv]
      rfl
  have hEval (w : InfinitePlace F) : ∃ z₁, (E w z₁)⁻¹ ≠ 0 := by
    by_cases hw : w.IsReal
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_real η w hw
      refine ⟨1 - b, ?_⟩
      simp only [E, c, hb, sub_add_cancel]
      exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_complex η w
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)
      refine ⟨1 - b, ?_⟩
      simp only [E, c, hb, sub_add_cancel]
      simp [Complex.Gammaℂ_def, Real.pi_ne_zero]
  have hmer (w : InfinitePlace F) : MeromorphicAt (E w) s := by
    convert ((hEinv w).analyticAt s).meromorphicAt.inv using 1
    funext z
    simp
  have hntop (w : InfinitePlace F) : meromorphicOrderAt (E w) s ≠ ⊤ := by
    intro htop
    have h1 : meromorphicOrderAt (fun z ↦ (E w z)⁻¹) s = ⊤ := by
      rw [show meromorphicOrderAt (fun z ↦ (E w z)⁻¹) s = -meromorphicOrderAt (E w) s from
        meromorphicOrderAt_inv, htop]
      rfl
    rw [((hEinv w).analyticAt s).meromorphicOrderAt_eq] at h1
    have h2 : analyticOrderAt (fun z ↦ (E w z)⁻¹) s = ⊤ := by
      cases hn : analyticOrderAt (fun z ↦ (E w z)⁻¹) s with
      | top => rfl
      | coe n => rw [hn] at h1; simp at h1
    have hA : AnalyticOnNhd ℂ (fun z ↦ (E w z)⁻¹) univ := fun z _ ↦ (hEinv w).analyticAt z
    obtain ⟨z₁, hz₁⟩ := hEval w
    exact hz₁ (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ s) (analyticOrderAt_eq_top.1 h2) (mem_univ z₁))
  have hle (w : InfinitePlace F) : meromorphicOrderAt (E w) s ≤ 0 := by
    have h0 := ((hEinv w).analyticAt s).meromorphicOrderAt_nonneg
    rw [show meromorphicOrderAt (fun z ↦ (E w z)⁻¹) s = -meromorphicOrderAt (E w) s from
      meromorphicOrderAt_inv] at h0
    cases hn : meromorphicOrderAt (E w) s with
    | top => exact absurd hn (hntop w)
    | coe n =>
      rw [hn] at h0
      have h0' : (0 : ℤ) ≤ -n := by exact_mod_cast h0
      exact_mod_cast (by omega : n ≤ 0)
  have key := sLocalArchimedeanPoleMultiplicity_eq_sum η s
  have hG : meromorphicOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s =
      ((sLocalArchimedeanPoleMultiplicity η s : ℤ) : WithTop ℤ) := by
    rw [show meromorphicOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s =
        -meromorphicOrderAt (fun z ↦ heckeGammaFactor χ z) s from meromorphicOrderAt_inv,
      hprod, meromorphicOrderAt_prod fun w _ ↦ hmer w,
      Finset.sum_congr rfl fun w _ ↦ (min_eq_right (hle w)).symm]
    change -(∑ w, min 0 (meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (c z))) s)) = _
    rw [← key]
    exact_mod_cast neg_neg (sLocalArchimedeanPoleMultiplicity η s : ℤ)
  rw [((differentiable_inv_heckeGammaFactor χ).analyticAt s).meromorphicOrderAt_eq] at hG
  cases hn : analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s with
  | top => rw [hn] at hG; simp at hG
  | coe n =>
    rw [hn] at hG
    have hn' : (n : ℤ) = (sLocalArchimedeanPoleMultiplicity η s : ℤ) := by simpa using hG
    simpa using hn'

/-- The reciprocal Gamma function vanishes to order at most one everywhere, by the
recursion `1/Γ(s) = s · 1/Γ(s + 1)`. -/
private theorem archNuclearity_trace_gammaInv_order_le (w : ℂ) :
    analyticOrderAt (fun s ↦ (Complex.Gamma s)⁻¹) w ≤ 1 := by
  have han (z : ℂ) : AnalyticAt ℂ (fun s ↦ (Complex.Gamma s)⁻¹) z :=
    Complex.differentiable_one_div_Gamma.analyticAt z
  by_cases hw : (Complex.Gamma w)⁻¹ = 0
  · obtain ⟨n, rfl⟩ := (Complex.Gamma_eq_zero_iff w).mp (inv_eq_zero.mp hw)
    induction n with
    | zero =>
      have hrec : (fun s ↦ (Complex.Gamma s)⁻¹) =
          (fun s : ℂ ↦ s - 0) * ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ s + 1)) := by
        funext s
        simp [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s]
      rw [hrec, analyticOrderAt_mul (by fun_prop) ((han _).comp (by fun_prop)),
        analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
      simp only [Nat.cast_zero, neg_zero]
      rw [analyticOrderAt_id_sub_const_self, zero_add,
        ((han 1).analyticOrderAt_eq_zero).mpr (by simp)]
      simp
    | succ n ih =>
      have hrec : (fun s ↦ (Complex.Gamma s)⁻¹) =
          (fun s : ℂ ↦ s) * ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ s + 1)) := by
        funext s
        simp [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s]
      rw [hrec, analyticOrderAt_mul (by fun_prop) ((han _).comp (by fun_prop)),
        analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
      have h0 : analyticOrderAt (fun s : ℂ ↦ s) (-((n + 1 : ℕ) : ℂ)) = 0 :=
        (analyticAt_id.analyticOrderAt_eq_zero).mpr (by
          show -(((n + 1 : ℕ) : ℂ)) ≠ 0
          rw [neg_ne_zero, Nat.cast_ne_zero]
          exact Nat.succ_ne_zero n)
      have h1 : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
      rw [h0, zero_add, h1]
      exact ih (by
        rw [inv_eq_zero]
        exact Complex.Gamma_neg_nat_eq_zero n)
  · rw [((han w).analyticOrderAt_eq_zero).mpr hw]
    exact zero_le

/-- A nonvanishing analytic factor times the reciprocal Gamma function at an affine
argument vanishes to order at most one. -/
private theorem archNuclearity_trace_affine_order_le (u : ℂ → ℂ) (a c z : ℂ) (ha : a ≠ 0)
    (hu : AnalyticAt ℂ u z) (hu0 : u z ≠ 0) :
    analyticOrderAt (fun s ↦ u s * (Complex.Gamma (a * s + c))⁻¹) z ≤ 1 := by
  have hg : AnalyticAt ℂ (fun s : ℂ ↦ a * s + c) z := by fun_prop
  have hΓ : AnalyticAt ℂ ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ a * s + c)) z :=
    (Complex.differentiable_one_div_Gamma.analyticAt _).comp hg
  change analyticOrderAt (u * ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ a * s + c))) z ≤ 1
  rw [analyticOrderAt_mul hu hΓ, (hu.analyticOrderAt_eq_zero).mpr hu0, zero_add,
    analyticOrderAt_comp_of_deriv_ne_zero hg (by
      rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'']
      simpa using ha)]
  exact archNuclearity_trace_gammaInv_order_le _

/-- The reciprocal of an archimedean Gamma factor is entire, vanishes to order at most
one, and vanishes only at `-c - k` for natural `k`. -/
private theorem archNuclearity_trace_factor (f : ℂ → ℂ) (c : ℂ)
    (hf : (∀ s, f s = Complex.Gammaℝ (s + c)) ∨ (∀ s, f s = Complex.Gammaℂ (s + c) / 2))
    (z : ℂ) :
    AnalyticAt ℂ (fun s ↦ (f s)⁻¹) z ∧ analyticOrderAt (fun s ↦ (f s)⁻¹) z ≤ 1 ∧
      ((f z)⁻¹ = 0 → ∃ k : ℕ, z = -c - k) := by
  rcases hf with hf | hf
  · have he : (fun s ↦ (f s)⁻¹) = fun s ↦ ((Real.pi : ℂ) ^ (-(s + c) / 2))⁻¹ *
        (Complex.Gamma ((1 / 2 : ℂ) * s + c / 2))⁻¹ := by
      funext s
      rw [hf, Complex.Gammaℝ_def, mul_inv, show (s + c) / 2 = 1 / 2 * s + c / 2 by ring]
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hu : Differentiable ℂ fun s : ℂ ↦ ((Real.pi : ℂ) ^ (-(s + c) / 2))⁻¹ :=
      fun s ↦ ((((differentiable_id.add_const c).neg.div_const 2) s).const_cpow
        (Or.inl hπ)).inv (Complex.cpow_ne_zero_iff.mpr (Or.inl hπ))
    refine ⟨?_, ?_, fun h0 ↦ ?_⟩
    · rw [he]
      exact (hu.analyticAt z).mul ((Complex.differentiable_one_div_Gamma.analyticAt _).comp
        (by fun_prop))
    · rw [he]
      exact archNuclearity_trace_affine_order_le _ _ _ z (by norm_num) (hu.analyticAt z)
        (inv_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)))
    · rw [hf] at h0
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp (inv_eq_zero.mp h0)
      exact ⟨2 * n, by push_cast; linear_combination hn⟩
  · have he : (fun s ↦ (f s)⁻¹) = fun s ↦ (2 * (2 * (2 * Real.pi : ℂ) ^ (-(s + c)))⁻¹) *
        (Complex.Gamma (1 * s + c))⁻¹ := by
      funext s
      rw [hf, Complex.Gammaℂ_def, one_mul]
      simp only [div_eq_mul_inv, mul_inv, inv_inv]
      ring
    have h2π : (2 * Real.pi : ℂ) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hpow (s : ℂ) : (2 * Real.pi : ℂ) ^ (-(s + c)) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl h2π)
    have hu : Differentiable ℂ fun s : ℂ ↦ 2 * (2 * (2 * Real.pi : ℂ) ^ (-(s + c)))⁻¹ :=
      fun s ↦ ((((differentiable_id.add_const c).neg s).const_cpow (Or.inl h2π)).const_mul
        2).inv (mul_ne_zero two_ne_zero (hpow s)) |>.const_mul 2
    refine ⟨?_, ?_, fun h0 ↦ ?_⟩
    · rw [he]
      exact (hu.analyticAt z).mul ((Complex.differentiable_one_div_Gamma.analyticAt _).comp
        (by fun_prop))
    · rw [he]
      exact archNuclearity_trace_affine_order_le _ _ _ z one_ne_zero (hu.analyticAt z)
        (mul_ne_zero two_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero (hpow z))))
    · rw [hf, inv_eq_zero, div_eq_zero_iff, Complex.Gammaℂ_def] at h0
      have hΓ : Complex.Gamma (z + c) = 0 := by
        rcases h0 with h0 | h0
        · rcases mul_eq_zero.mp h0 with h | h
          · exact absurd h (mul_ne_zero two_ne_zero (hpow z))
          · exact h
        · exact absurd h0 two_ne_zero
      obtain ⟨n, hn⟩ := (Complex.Gamma_eq_zero_iff _).mp hΓ
      exact ⟨n, by linear_combination hn⟩

/-- The reciprocal of a finite product of archimedean Gamma factors vanishes to order at
most the number of factors, and only at points `-c i - k`. -/
private theorem archNuclearity_trace_prod {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (c : ι → ℂ) (hf : ∀ i, (∀ s, f i s = Complex.Gammaℝ (s + c i)) ∨
      (∀ s, f i s = Complex.Gammaℂ (s + c i) / 2)) (z : ℂ) :
    analyticOrderAt (fun s ↦ (∏ i, f i s)⁻¹) z ≤ Fintype.card ι ∧
      ((∏ i, f i z)⁻¹ = 0 → ∃ i, ∃ k : ℕ, z = -c i - k) := by
  classical
  have hinv : (fun s ↦ (∏ i, f i s)⁻¹) = fun s ↦ ∏ i, (f i s)⁻¹ := by
    funext s
    rw [Finset.prod_inv_distrib]
  refine ⟨?_, fun h0 ↦ ?_⟩
  · rw [hinv, ← Finset.card_univ]
    have key : ∀ s : Finset ι, AnalyticAt ℂ (fun w ↦ ∏ i ∈ s, (f i w)⁻¹) z ∧
        analyticOrderAt (fun w ↦ ∏ i ∈ s, (f i w)⁻¹) z ≤ s.card := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        refine ⟨by simpa using analyticAt_const, ?_⟩
        simp only [Finset.prod_empty, Finset.card_empty, Nat.cast_zero]
        exact ((analyticAt_const).analyticOrderAt_eq_zero.mpr one_ne_zero).le
      | insert a s ha ih =>
        obtain ⟨hfa, hoa, -⟩ := archNuclearity_trace_factor (f a) (c a) (hf a) z
        have he : (fun w ↦ ∏ i ∈ insert a s, (f i w)⁻¹) =
            (fun w ↦ (f a w)⁻¹) * fun w ↦ ∏ i ∈ s, (f i w)⁻¹ := by
          funext w
          rw [Finset.prod_insert ha]
          rfl
        rw [he]
        refine ⟨hfa.mul ih.1, ?_⟩
        rw [analyticOrderAt_mul hfa ih.1, Finset.card_insert_of_notMem ha, Nat.cast_add,
          Nat.cast_one, add_comm (s.card : ℕ∞)]
        exact add_le_add hoa ih.2
    exact (key Finset.univ).2
  · rw [← Finset.prod_inv_distrib, Finset.prod_eq_zero_iff] at h0
    obtain ⟨i, -, hi⟩ := h0
    obtain ⟨k, hk⟩ := (archNuclearity_trace_factor (f i) (c i) (hf i) z).2.2 hi
    exact ⟨i, k, hk⟩

/-- The reciprocal archimedean gamma factor of `χ` vanishes to order at most the number of
infinite places, and only at points `-c v - k` with `k` a natural number. -/
private theorem archNuclearity_trace_gammaOrder :
    ∃ c : InfinitePlace F → ℂ, ∀ z : ℂ, gammaOrder(χ, z) ≤ Fintype.card (InfinitePlace F) ∧
      (0 < gammaOrder(χ, z) → ∃ v, ∃ k : ℕ, z = -c v - k) := by
  let G : InfinitePlace F → ℂ → ℂ := fun v s ↦ if hv : v.IsReal then
      Complex.Gammaℝ (s + (realHeckeCharacter_parameters χ v hv).exists.choose.1 +
        ((realHeckeCharacter_parameters χ v hv).exists.choose.2.val : ℂ))
    else Complex.Gammaℂ (s + (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.1 +
        ((complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.2.natAbs : ℂ) / 2) / 2
  let c : InfinitePlace F → ℂ := fun v ↦ if hv : v.IsReal then
      (realHeckeCharacter_parameters χ v hv).exists.choose.1 +
        ((realHeckeCharacter_parameters χ v hv).exists.choose.2.val : ℂ)
    else (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.1 +
        ((complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.2.natAbs : ℂ) / 2
  have hG (s : ℂ) : heckeGammaFactor χ s = ∏ v, G v s := by
    unfold heckeGammaFactor
    rfl
  have hc (v : InfinitePlace F) : (∀ s, G v s = Complex.Gammaℝ (s + c v)) ∨
      (∀ s, G v s = Complex.Gammaℂ (s + c v) / 2) := by
    by_cases hv : v.IsReal
    · exact Or.inl fun s ↦ by simp only [G, c, hv, ↓reduceDIte, add_assoc]
    · exact Or.inr fun s ↦ by simp only [G, c, hv, ↓reduceDIte, add_assoc]
  refine ⟨c, fun z ↦ ?_⟩
  have hfun : (fun s ↦ (heckeGammaFactor χ s)⁻¹) = fun s ↦ (∏ v, G v s)⁻¹ :=
    funext fun s ↦ by rw [hG]
  obtain ⟨hord, hzero⟩ := archNuclearity_trace_prod G c hc z
  have han := (differentiable_inv_heckeGammaFactor χ).analyticAt z
  constructor
  · rw [hfun]
    cases h : analyticOrderAt (fun s ↦ (∏ v, G v s)⁻¹) z with
    | top => simp
    | coe n =>
      rw [h] at hord
      simpa using hord
  · intro hpos
    apply hzero
    rw [← hG]
    by_contra hne
    rw [(han.analyticOrderAt_eq_zero).mpr hne] at hpos
    simp at hpos

/-- Paper: Theorem 7.4.3.1(2), p. 368.
The raw total pole order is reduced by one at the trivial quasi-character,
when it lies on the chosen component.
Deviation: Page 368 names the quasi-character |·|^(it₀). The chart parameter it₀
corresponds to the trivial quasi-character when χ = |·|^(−it₀). -/
def archNuclearityMultiplicity (s : ℂ) : ℕ :=
  gammaOrder(χ, s) - if ω(χ) = 1 ∧ s = atZeroPole(χ, τ, hτ) then 1 else 0

/-- Paper: Theorem 7.4.3.1(2), p. 368.
For the trivial rational character, the adjusted order at zero vanishes and the
simple gamma pole at minus two remains. -/
theorem archNuclearityMultiplicity_rat_one
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 ℚ) ℚ) (hτ : RightInverse τ (ideleNorm ℚ)) :
    archNuclearityMultiplicity (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) τ hτ 0 = 0 ∧
      archNuclearityMultiplicity (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) τ hτ (-2) = 1 :=
  by
  have hphase := existsUnique_ideleNormSection_character_phase
    (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) τ hτ
  have hx : hphase.exists.choose = 0 :=
    hphase.unique hphase.exists.choose_spec fun t ↦ by simp
  have hω : (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm ℚ).ker →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) = 1 :=
    ContinuousMonoidHom.ext fun _ ↦ rfl
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hπz (z : ℂ) : (Real.pi : ℂ) ^ (z / 2) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hπ)
  have hG (z : ℂ) : (heckeGammaFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)⁻¹ =
      (Real.pi : ℂ) ^ (z / 2) * (z / 2 * ((z / 2 + 1) * (Complex.Gamma (z / 2 + 1 + 1))⁻¹)) := by
    rw [heckeGammaFactor_one,
      InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ),
      InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ),
      pow_one, pow_zero, mul_one, Complex.Gammaℝ, mul_inv, neg_div, Complex.cpow_neg, inv_inv,
      Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one,
      Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z / 2 + 1)]
  have hpow : Differentiable ℂ fun z : ℂ ↦ (Real.pi : ℂ) ^ (z / 2) :=
    (differentiable_id.div_const 2).const_cpow (Or.inl hπ)
  have hΓ : Differentiable ℂ fun z : ℂ ↦ (Complex.Gamma (z / 2 + 1 + 1))⁻¹ :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  have hf : Differentiable ℂ fun z ↦
      (heckeGammaFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)⁻¹ := by
    simp only [hG]
    exact hpow.mul ((differentiable_id.div_const 2).mul
      (((differentiable_id.div_const 2).add_const 1).mul hΓ))
  have hΓne (z : ℂ) (hz : 0 < z.re) : (Complex.Gamma z)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos hz)
  have h0 : (analyticOrderAt (fun z ↦
      (heckeGammaFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)⁻¹) 0).toNat = 1 := by
    rw [((hf.analyticAt 0).analyticOrderAt_eq_natCast (n := 1)).2 ⟨fun z ↦
      (Real.pi : ℂ) ^ (z / 2) * (1 / 2 * ((z / 2 + 1) * (Complex.Gamma (z / 2 + 1 + 1))⁻¹)),
      (hpow.mul ((differentiable_const _).mul
        (((differentiable_id.div_const 2).add_const 1).mul hΓ))).analyticAt 0, ?_,
      Filter.Eventually.of_forall fun z ↦ ?_⟩]
    · rfl
    · refine mul_ne_zero (hπz 0) (mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num)
        (hΓne _ (by norm_num))))
    · rw [hG, smul_eq_mul]
      ring
  have h2 : (analyticOrderAt (fun z ↦
      (heckeGammaFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)⁻¹) (-2)).toNat = 1 := by
    rw [((hf.analyticAt (-2)).analyticOrderAt_eq_natCast (n := 1)).2 ⟨fun z ↦
      (Real.pi : ℂ) ^ (z / 2) * (z / 2 * (1 / 2 * (Complex.Gamma (z / 2 + 1 + 1))⁻¹)),
      (hpow.mul ((differentiable_id.div_const 2).mul
        ((differentiable_const _).mul hΓ))).analyticAt (-2), ?_,
      Filter.Eventually.of_forall fun z ↦ ?_⟩]
    · rfl
    · refine mul_ne_zero (hπz _) (mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num)
        (hΓne _ (by norm_num))))
    · rw [hG, smul_eq_mul]
      ring
  refine ⟨?_, ?_⟩ <;> unfold archNuclearityMultiplicity
  · rw [h0, hx]
    simp [hω]
  · rw [h2, hx]
    simp

/-- Paper: Theorem 7.4.3.1(2), p. 368.
Each pole contributes derivative indices from zero up to its adjusted order. -/
abbrev ArchNuclearityJetIndex := {j : ℂ × ℕ // j.2 < archNuclearityMultiplicity χ τ hτ j.1}

/-- Paper: Equation (7.4.3.4), p. 368.
The orbital jet applies a continuous entire derivative to the Mellin transform of
a zero-moment theta class. -/
def archNuclearityJet (j : ArchNuclearityJetIndex χ τ hτ) : StrongDual ℂ (Θ₀(χ)) :=
  ((entireJet j.val.1 j.val.2).comp schwartzBergmanEntireInclusion).comp (Z(χ, τ, hτ))

section AdjustedJetRealization

local notation "completedGenerator" => regularizedCompletedHeckeL χ τ hτ
  (continuedCompletedHeckeL χ) (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2

/-- Reflection preserves the meromorphic order. The inverse character has no zero
at or to the right of the line of absolute convergence. -/
private theorem archJet_completed_order_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) s ≤ 0 := by
  obtain ⟨ε, hε, hne, he⟩ := completedHeckeL_continuation_functionalEquation χ
    (continuedCompletedHeckeL χ) (continuedCompletedHeckeL χ⁻¹)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
  let r (z : ℂ) := 1 - z
  have hr : HasDerivAt r (-1) s := by simpa [r] using (hasDerivAt_id s).const_sub 1
  have e : continuedCompletedHeckeL χ⁻¹ ∘ r = fun z ↦ ε z * continuedCompletedHeckeL χ z :=
    funext he
  have ho := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹)
    (show AnalyticAt ℂ r s by dsimp [r]; fun_prop) (hr.deriv.trans_ne (by norm_num))
  rw [e] at ho
  change meromorphicOrderAt (ε * continuedCompletedHeckeL χ) s = _ at ho
  rw [meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt s) (hne s)] at ho
  rw [ho]
  have hright : 1 ≤ (r s).re := by change 1 ≤ 1 - s.re; linarith
  exact le_of_not_gt (fun hz ↦ (completedHeckeL_continuation_zeros χ⁻¹ _
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
    (zero_lt_one.trans_le hright) hz).not_ge hright)

/-- The entire pole-removed factor is nonzero throughout the closed left half-plane. -/
private theorem archJet_regularized_nonzero {s : ℂ} (hs : s.re ≤ 0) : (completedGenerator).val s ≠ 0 := by
  classical
  let L := continuedCompletedHeckeL χ
  let b := (((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℝ) : ℂ) * Complex.I
  let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
  let polePolynomial (z : ℂ) := (z + b) ^ δ * (1 - z - b) ^ δ
  have hL := (continuedCompletedHeckeL_spec χ).1
  by_cases hcan : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 ∧ (s = -b ∨ s = 1 - b)
  · have hp := regularizedCompletedHeckeL_ne_zero_at_canceled_poles χ τ hτ L hL
      (continuedCompletedHeckeL_spec χ).2 hcan.1
    rcases hcan.2 with rfl | rfl
    · exact hp.1
    · exact hp.2
  have hP : polePolynomial s ≠ 0 := by
    by_cases htriv : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · have h := not_or.mp (fun hh ↦ hcan ⟨htriv,hh⟩)
      simp only [polePolynomial, δ, ite_eq_left htriv, pow_one]
      refine mul_ne_zero (fun hz ↦ h.1 (eq_neg_of_add_eq_zero_left hz)) ?_
      intro hz
      apply h.2
      linear_combination -hz
    · simp [polePolynomial, δ, htriv]
  have hPa (z : ℂ) : AnalyticAt ℂ polePolynomial z := by dsimp [polePolynomial]; fun_prop
  have hPL : MeromorphicOn (polePolynomial * L) univ := fun z hz ↦
    (hPa z).meromorphicAt.mul (hL hz).meromorphicAt
  have he : ((completedGenerator).val : ℂ → ℂ) = toMeromorphicNFOn (polePolynomial * L) univ := rfl
  have hor : meromorphicOrderAt ((completedGenerator).val : ℂ → ℂ) s = meromorphicOrderAt L s := by
    rw [he, meromorphicOrderAt_toMeromorphicNFOn hPL (mem_univ _),
      meromorphicOrderAt_mul_of_ne_zero (hPa s) hP]
  have ha := (completedGenerator).property.analyticAt s
  apply ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
  exact le_antisymm (hor.trans_le (archJet_completed_order_nonpos χ hs)) ha.meromorphicOrderAt_nonneg

private theorem archJet_completed_nonzero (ρ : ℂ) (hρ : 0 < archNuclearityMultiplicity χ τ hτ ρ) :
    (completedGenerator).val ρ ≠ 0 := by
  apply archJet_regularized_nonzero χ τ hτ
  by_contra! hpos
  have hn := inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hpos)
  have hzero := ((differentiable_inv_heckeGammaFactor χ).analyticAt ρ).analyticOrderAt_eq_zero.mpr hn
  simp [archNuclearityMultiplicity, hzero] at hρ

/-- Only finitely many adjusted gamma pole centres lie to the right of a given line.
The multiplicities are bounded by the number of infinite places. -/
private theorem archJet_support_finite :
    (∀ z, archNuclearityMultiplicity χ τ hτ z ≤ Fintype.card (InfinitePlace F)) ∧
      ∀ a : ℝ, {z : ℂ | 0 < archNuclearityMultiplicity χ τ hτ z ∧ a ≤ z.re}.Finite := by
  classical
  obtain ⟨c, hc⟩ := archNuclearity_trace_gammaOrder χ
  have hle (z : ℂ) : archNuclearityMultiplicity χ τ hτ z ≤ gammaOrder(χ, z) :=
    Nat.sub_le _ _
  refine ⟨fun z ↦ (hle z).trans (hc z).1, fun a ↦ ?_⟩
  choose N hN using fun v : InfinitePlace F ↦ exists_nat_gt (-(c v).re - a)
  let T (v : InfinitePlace F) := (fun k : ℕ ↦ -c v - (k : ℂ)) '' Iic (N v)
  have hT (v : InfinitePlace F) : (T v).Finite :=
    (finite_Iic (N v)).image (fun k : ℕ ↦ -c v - (k : ℂ))
  refine (finite_iUnion hT).subset fun z hz ↦ ?_
  obtain ⟨v, k, rfl⟩ := (hc z).2 (hz.1.trans_le (hle z))
  have hz' : a ≤ -(c v).re - (k : ℝ) := by
    simpa only [Complex.sub_re, Complex.neg_re, Complex.natCast_re] using hz.2
  have hk : (k : ℝ) < (N v : ℝ) := by linarith [hN v]
  exact mem_iUnion.mpr ⟨v, k, (by exact_mod_cast hk.le : k ≤ N v), rfl⟩

private theorem archJet_surjective :
    Function.Surjective (fun (x : Θ₀(χ)) j ↦ archNuclearityJet χ τ hτ j x) := by
  intro c
  obtain ⟨hord, hfin⟩ := archJet_support_finite χ τ hτ
  let d := Fintype.card (InfinitePlace F) + 1
  let L := continuedCompletedHeckeL χ
  obtain ⟨hL, hEq⟩ := continuedCompletedHeckeL_spec χ
  have hΛ : orbitalHeckeGenerator χ τ hτ L hL hEq ∅ = completedGenerator :=
    orbitalHeckeGenerator_empty χ τ hτ L hL hEq
  have hne (z : ℂ) (hz : 0 < archNuclearityMultiplicity χ τ hτ z) :
      (orbitalHeckeGenerator χ τ hτ L hL hEq ∅).val z ≠ 0 := by
    rw [hΛ]
    exact archJet_completed_nonzero χ τ hτ z hz
  obtain ⟨f, hf, hjet⟩ := orbitalSchwartzBergman_jetInterpolation χ τ hτ L hL hEq ∅
    (archNuclearityMultiplicity χ τ hτ) d (Nat.succ_pos _) (fun z ↦ (hord z).trans (Nat.le_succ _))
    hfin hne c
  rw [hΛ] at hf
  obtain ⟨x, hx⟩ := (specDenom_range_mem χ τ hτ f).2 ((specDenom_mem_div _ f).1 hf)
  refine ⟨x, funext fun j ↦ ?_⟩
  change archNuclearityJet χ τ hτ j x = c j
  unfold archNuclearityJet
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply, hx]
  have heq : ((schwartzBergmanEntireInclusion f).val : ℂ → ℂ) = f.val :=
    funext (schwartzBergmanEntireInclusion_apply f)
  rw [heq]
  exact hjet j

end AdjustedJetRealization

/-- Paper: Equation (7.4.3.4), p. 368.
On a representative the orbital jet is the derivative of the idelic zeta integral.
Its inverse Mellin formula is the convergent logarithmic moment.
Deviation: Uses the normalized inverse Mellin transform, including the missing
factor 1/(2πi) in the printed vertical integral. -/
theorem archNuclearityJet_apply (j : ArchNuclearityJetIndex χ τ hτ) (f : P) :
    let u : ℂ → ℂ := ((Z(χ, τ, hτ)) mkΘ(χ, f)).val
    let moment := fun t : ℝ ↦ (Real.log t : ℂ) ^ j.val.2 * mellinInv 0 u t
    Complex.VerticalIntegrable u 0 ∧ MellinConvergent moment j.val.1.re ∧
      archNuclearityJet χ τ hτ j mkΘ(χ, f) =
        iteratedDeriv j.val.2 (fun s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s)) j.val.1 ∧
      archNuclearityJet χ τ hτ j mkΘ(χ, f) = mellin moment j.val.1 := by
  let v : B := (Z(χ, τ, hτ)) mkΘ(χ, f)
  have hmoment := schwartzBergman_jet_eq_mellinInv_moment v j.val.1 j.val.2
  have hz : (v.val : ℂ → ℂ) = (fun s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s)) :=
    funext fun s ↦ ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f s).2
  have hjet : archNuclearityJet χ τ hτ j mkΘ(χ, f) = iteratedDeriv j.val.2 v.val j.val.1 := by
    unfold archNuclearityJet
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
    exact congrArg (fun g : ℂ → ℂ ↦ iteratedDeriv j.val.2 g j.val.1)
      (funext (schwartzBergmanEntireInclusion_apply v))
  exact ⟨hmoment.1, hmoment.2.1, hjet.trans (congrArg (fun g : ℂ → ℂ ↦
    iteratedDeriv j.val.2 g j.val.1) hz), hjet.trans hmoment.2.2⟩

/-- At one infinite place the gamma factor vanishes, by Mathlib's convention at the poles
of `Γ`, along an arithmetic progression. So the reciprocal gamma product has a zero of
positive finite order at infinitely many points. -/
private theorem archNuclearityJet_basis_poles_infinite
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    {s : ℂ | 0 < gammaOrder(χ, s)}.Infinite := by
  classical
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let c : ℂ := if hv : v.IsReal then
      (realHeckeCharacter_parameters χ v hv).exists.choose.1 +
        ((realHeckeCharacter_parameters χ v hv).exists.choose.2.val : ℂ)
    else
      (complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.1 +
        ((complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.2.natAbs : ℂ) / 2
  let s : ℕ → ℂ := fun n ↦ -c - 2 * n
  have hzero (n : ℕ) : heckeGammaFactor χ (s n) = 0 := by
    unfold heckeGammaFactor
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    by_cases hv : v.IsReal
    · simp only [s, c, hv, ↓reduceDIte]
      rw [Complex.Gammaℝ_eq_zero_iff]
      exact ⟨n, by ring⟩
    · simp only [s, c, hv, ↓reduceDIte]
      rw [div_eq_zero_iff]
      left
      rw [show -(_ + _) - 2 * (n : ℂ) + _ + _ = -((2 * n : ℕ) : ℂ) by push_cast; ring,
        Complex.Gammaℂ_def, Complex.Gamma_neg_nat_eq_zero, mul_zero]
  let f := fun z ↦ (heckeGammaFactor χ z)⁻¹
  have hA : AnalyticOnNhd ℂ f univ :=
    fun z _ ↦ (differentiable_inv_heckeGammaFactor χ).analyticAt z
  have hpos (n : ℕ) : s n ∈ {s : ℂ | 0 < gammaOrder(χ, s)} := by
    have h0 : analyticOrderAt f (s n) ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hA _ (mem_univ _), by simp [f, hzero n]⟩
    have htop : analyticOrderAt f (s n) ≠ ⊤ := by
      intro htop
      have h1 := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (mem_univ (s n)) (analyticOrderAt_eq_top.1 htop) (mem_univ 1)
      exact inv_ne_zero
        (heckeGammaFactor_ne_zero_of_re_pos χ (by norm_num : (0 : ℝ) < (1 : ℂ).re)) h1
    change 0 < (analyticOrderAt f (s n)).toNat
    cases hn : analyticOrderAt f (s n) with
    | top => exact absurd hn htop
    | coe m =>
      rw [hn] at h0
      simpa [Nat.pos_iff_ne_zero] using h0
  refine Set.infinite_of_injective_forall_mem (fun n m h ↦ ?_) hpos
  have := congrArg Complex.re h
  simp only [s, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im] at this
  norm_num at this
  exact_mod_cast this

/-- The adjusted jet indices are countably infinite: they lie over the closed discrete
pole set, and the adjustment removes at most one index from an infinite pole set. -/
private theorem archNuclearityJet_basis_index_equiv
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F)) :
    Nonempty (ℕ ≃ ArchNuclearityJetIndex χ τ hτ) := by
  let S := {s : ℂ | 0 < gammaOrder(χ, s)}
  have hS : S.Countable := by
    have hd := (archNuclearityPoleSet_discrete χ).2
    have : DiscreteTopology S := hd.to_subtype
    exact Set.countable_coe_iff.mp
      (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)
  have hmem (j : ArchNuclearityJetIndex χ τ hτ) : j.val.1 ∈ S := by
    have h := j.property
    unfold archNuclearityMultiplicity at h
    show 0 < gammaOrder(χ, j.val.1)
    omega
  have : Countable (ArchNuclearityJetIndex χ τ hτ) := by
    have := hS.to_subtype
    refine Function.Injective.countable
      (f := fun j : ArchNuclearityJetIndex χ τ hτ ↦ ((⟨j.val.1, hmem j⟩ : S), j.val.2)) ?_
    intro a b h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  have : Infinite (ArchNuclearityJetIndex χ τ hτ) := by
    have := ((archNuclearityJet_basis_poles_infinite χ).sdiff
      (Set.finite_singleton (atZeroPole(χ, τ, hτ)))).to_subtype
    refine Infinite.of_injective
      (fun s : ↥(S \ {atZeroPole(χ, τ, hτ)}) ↦
        (⟨(s.val, 0), ?_⟩ : ArchNuclearityJetIndex χ τ hτ)) ?_
    · have hs := s.property
      simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hs
      change 0 < archNuclearityMultiplicity χ τ hτ s.val
      unfold archNuclearityMultiplicity
      have hne : ¬(ω(χ) = 1 ∧ s.val = atZeroPole(χ, τ, hτ)) := fun h ↦ hs.2 h.2
      simp only [hne, ↓reduceIte, Nat.sub_zero]
      simpa [S] using hs.1
    · intro a b h
      exact Subtype.ext (congrArg (fun j : ArchNuclearityJetIndex χ τ hτ ↦ j.val.1) h)
  exact ⟨(nonempty_equiv_of_countable (α := ArchNuclearityJetIndex χ τ hτ)).some.symm⟩

local notation "finiteL(" χ ")" => (finiteHeckeL_exists_continuation χ).choose
local notation "poleFactor(" χ ", " τ ", " hτ ", " s ")" =>
  ((s : ℂ) - 1 - atZeroPole(χ, τ, hτ)) ^ (if ω(χ) = 1 then (1 : ℕ) else 0)

private theorem archRegularizedFiniteHeckeL_cancel_simplePole {A Z : ℂ → ℂ} {z : ℂ}
    (ha : AnalyticAt ℂ A z) (hvan : A z = 0)
    (hZ : MeromorphicAt Z z) (hpole : meromorphicOrderAt Z z = -1) :
    0 ≤ meromorphicOrderAt (A * Z) z := by
  have hpos : 0 < meromorphicOrderAt A z := lt_of_le_of_ne ha.meromorphicOrderAt_nonneg
    (fun he ↦ ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp he.symm hvan)
  rw [meromorphicOrderAt_mul ha.meromorphicAt hZ, hpole]
  cases ho : meromorphicOrderAt A z with
  | top => simp
  | coe k =>
    rw [ho] at hpos
    have hk : (0 : ℤ) < k := WithTop.coe_lt_coe.mp hpos
    exact WithTop.coe_le_coe.mpr (show (0 : ℤ) ≤ k + (-1) by omega)

/-- Paper: Equation (7.4.3.5), p. 368.
After cancellation of the pole on the trivial norm-one component, the continued
finite Hecke function is entire. -/
theorem archRegularizedFiniteHeckeL_differentiable :
    Differentiable ℂ (toMeromorphicNFOn
      (fun s ↦ poleFactor(χ, τ, hτ, s) * finiteL(χ) s) univ) := by
  let p : ℂ → ℂ := fun z ↦ poleFactor(χ, τ, hτ, z)
  let R : ℂ → ℂ := fun z ↦ (heckeGammaFactor χ z)⁻¹
  let L := finiteL(χ)
  let Z := continuedCompletedHeckeL χ
  obtain ⟨hL, heL⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  obtain ⟨hZ, heZ⟩ := continuedCompletedHeckeL_spec χ
  have hp : Differentiable ℂ p := by
    dsimp only [p]
    fun_prop
  have hR : Differentiable ℂ R := differentiable_inv_heckeGammaFactor χ
  have hA : Differentiable ℂ (p * R) := hp.mul hR
  have hm : MeromorphicOn ((p * R) * Z) univ := fun z _ ↦
    (hA.analyticAt z).meromorphicAt.mul (hZ (mem_univ z)).meromorphicAt
  change Differentiable ℂ (toMeromorphicNFOn (p * L) univ)
  rw [heckeEulerProductOutside_eq_finite_nf_eq (p * L) ((p * R) * Z)
    (fun z _ ↦ (hp.analyticAt z).meromorphicAt.mul (hL (mem_univ z)).meromorphicAt) hm (by
      intro z hz
      change p z * L z = p z * (heckeGammaFactor χ z)⁻¹ * Z z
      rw [show L z = _ from heL ⟨z, hz⟩, show Z z = _ from heZ ⟨z, hz⟩]
      change _ = p z * (heckeGammaFactor χ z)⁻¹ * (heckeGammaFactor χ z * _)
      rw [mul_assoc, inv_mul_cancel_left₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz))]
      rfl)]
  by_cases hk : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · have hω : ω(χ) = 1 := by
      ext1 u
      exact DFunLike.congr_fun hk u
    obtain ⟨t, ⟨hc, hzero, hone, haway⟩, -⟩ := completedHeckeL_continuation_simplePoles χ Z hZ heZ hk
    let b : ℂ := Complex.I * (t : ℂ)
    have hphase := existsUnique_ideleNormSection_character_phase χ τ hτ
    have hx : -t = hphase.exists.choose := by
      apply hphase.unique _ hphase.exists.choose_spec
      intro u
      have he := DFunLike.congr_fun hc (QuotientGroup.mk (τ u))
      change (χ (QuotientGroup.mk (τ u)) : ℂ) * _ ^ (0 : ℂ) =
        1 * ((((ideleNorm F (τ u)).val : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ))) at he
      rw [Complex.cpow_zero, mul_one, one_mul, hτ u] at he
      simpa only [Complex.ofReal_neg, neg_mul, mul_comm (t : ℂ) Complex.I] using he
    have hpole : atZeroPole(χ, τ, hτ) = b := by
      change -(hphase.exists.choose : ℂ) * Complex.I = b
      rw [← hx, Complex.ofReal_neg, neg_neg, mul_comm]
    have hz₀ : (p * R) b = 0 := by
      have hshift := heckeGammaFactor_of_normTwist χ (-Complex.I * (t : ℂ)) (by simp [Complex.mul_re]) hc b
      have hneg : b + -Complex.I * (t : ℂ) = 0 := by
        dsimp [b]
        ring
      have hg : R b = 0 := by
        change (heckeGammaFactor χ b)⁻¹ = 0
        rw [hshift, hneg]
        simpa using inv_heckeGammaFactor_one_neg_even (F := F) 0
      simp [hg]
    have hz₁ : (p * R) (1 + b) = 0 := by simp [p, hω, hpole]
    intro z
    apply AnalyticAt.differentiableAt
    apply (meromorphicNFOn_toMeromorphicNFOn _ _ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ _)]
    by_cases hz : z = b ∨ z = 1 + b
    · rcases hz with rfl | rfl
      · exact archRegularizedFiniteHeckeL_cancel_simplePole (hA.analyticAt _) hz₀
          (hZ (mem_univ _)).meromorphicAt hzero
      · exact archRegularizedFiniteHeckeL_cancel_simplePole (hA.analyticAt _) hz₁
          (hZ (mem_univ _)).meromorphicAt hone
    · exact ((hA.analyticAt z).mul (haway z (by simpa [b] using hz))).meromorphicOrderAt_nonneg
  · have hd := hA.mul (completedHeckeL_continuation_entire χ Z hZ heZ hk)
    rwa [toMeromorphicNFOn_eq_self.mpr (fun z _ ↦ (hd.analyticAt z).meromorphicNFAt)]

/-- Paper: Equation (7.4.3.5), p. 368.
The generator of the archimedean ideal is the pole-removed finite Hecke function.
Normal form supplies the removable value at its canceled pole. -/
def archRegularizedFiniteHeckeL : Entire :=
  let h := archRegularizedFiniteHeckeL_differentiable χ τ hτ
  ⟨⟨_, h.continuous⟩, h⟩

/-- Paper: Equation (7.4.3.5), p. 368.
On the half-plane of absolute convergence the generator equals the Euler product
times the pole-removing factor. -/
theorem archRegularizedFiniteHeckeL_apply (s : {s : ℂ // 1 < s.re}) :
    (archRegularizedFiniteHeckeL χ τ hτ).val s.val =
      poleFactor(χ, τ, hτ, s.val) * finiteHeckeL χ s := by
  let pole : ℂ → ℂ := fun z ↦ poleFactor(χ, τ, hτ, z)
  have hP (z : ℂ) : AnalyticAt ℂ pole z := by
    dsimp only [pole]
    fun_prop
  have hne : pole s ≠ 0 := by
    apply pow_ne_zero
    intro h
    have hr := congrArg Complex.re h
    have hs := s.property
    simp at hr
    linarith
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  have hm : MeromorphicOn (fun z ↦ pole z * finiteL(χ) z) univ :=
    fun z hz ↦ (hP z).meromorphicAt.mul (hL.1 hz).meromorphicAt
  have hNF : MeromorphicNFAt (fun z ↦ pole z * finiteL(χ) z) s :=
    (meromorphicNFAt_mul_iff_right (hP s) hne).2 (hL.1 (mem_univ _))
  change toMeromorphicNFOn (fun z ↦ pole z * finiteL(χ) z) univ s = pole s * finiteHeckeL χ s
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _),
    toMeromorphicNFAt_eq_self.mpr hNF]
  exact congrArg (pole s * ·) (hL.2 s)

-- TODO(paper-gap): Before (7.4.3.12) on p. 371, not every numerator class
-- comes from a flat test. For ℚ, S = {∞}, χ = 1, finite PV is the identity.
-- The real Gaussian combination in Printed.archNuclearityJet_apply_false has
-- nonzero global Z(-2), whereas a flat real test times the finite integer
-- indicator has Z(-2) = 0. Also, odd flat bumps have zero trivial theta class.
-- Apply §6.2 to homogeneous classes of polar tests, then identify the image
-- of the flat denominator under insertion. Uniqueness is a quotient assertion.
-- TODO(paper-gap): On p. 371, injectivity of the comparison quotient map requires
-- the range identification below. Density of the inclusion into entire functions
-- does not give that identification. Evaluations at nontrivial completed zeros
-- lie in the kernel of the printed adjoint to the theta annihilator. Pass to
-- the relative quotient of the completed ideal by the finite ideal.

/-- Splitting Haar measure on the ideles gives the same finite factor for every choice
of archimedean test paired with a fixed finite test. -/
private theorem archNuclearityQuotient_jetEquiv_annihilate_product
    (χ : U) (b : ℬ(FiniteAdeleRing (𝓞 F) F)) (s : ℂ) :
    ∃ factor : ℂ, ∀ a : ℬ(InfiniteAdeleRing F),
      globalIdelicZetaIntegral ((adeleSchwartz_inductiveTensor_equiv F).choose (a ⊗ₜ[ℂ] b))
          (ideleClassNormTwist χ s) =
        (∫ u : (SAdeleRing F ∅)ˣ, a (Multiplicative.ofAdd u.val.1) *
          ideleClassNormTwist χ s (QuotientGroup.mk (sIdeleInsertion F ∅ u))
          ∂sMultiplicativeTamagawaMeasure F ∅) * factor := by
  let A := (SAdeleRing F ∅)ˣ
  let Bf := (FiniteAdeleRing (𝓞 F) F)ˣ
  let I := IdeleGroup (𝓞 F) F
  let e₀ : (SAdeleRing F ∅) ≃ₜ* InfiniteAdeleRing F := ContinuousMulEquiv.mk'
    (Homeomorph.prodUnique _ (∀ v : (∅ : Finset V), v.val.adicCompletion F)) (fun _ _ ↦ rfl)
  let e₁ := Units.mapContinuousMulEquiv e₀
  let e₂ := (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).symm
  let e : A × Bf ≃ₜ* I := (ContinuousMulEquiv.mk'
    (e₁.toHomeomorph.prodCongr (Homeomorph.refl Bf)) (fun x y ↦ Prod.ext (map_mul e₁ _ _) rfl)).trans e₂
  let : MeasurableSpace I := borel _
  let : BorelSpace I := ⟨rfl⟩
  let : LocallyCompactSpace I := (ideleGroup_topology F).2.1
  let : SecondCountableTopology I := idele_secondCountable F
  let : LocallyCompactSpace (A × Bf) := e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology (A × Bf) := e.toHomeomorph.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace A := (isOpenQuotientMap_fst (Y := Bf)).locallyCompactSpace
  let : LocallyCompactSpace Bf := (isOpenQuotientMap_snd (X := A)).locallyCompactSpace
  let : SecondCountableTopology Bf := (isEmbedding_prodMkRight (X := A) (Y := Bf) 1).secondCountableTopology
  let : SecondCountableTopology A := (isEmbedding_prodMkLeft (X := A) (Y := Bf) 1).secondCountableTopology
  let : MeasurableSpace Bf := borel _
  let : BorelSpace Bf := ⟨rfl⟩
  let : MeasurableSpace (SAdeleRing F ∅) := instMeasurableSpaceSAdeleRing F ∅
  let : BorelSpace A := sIdeleGroup_borelSpace (F := F) (S := ∅)
  let μ := sMultiplicativeTamagawaMeasure F ∅
  let ν := (Measure.haar : Measure Bf)
  let : μ.IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := ∅)
  let m := (μ.prod ν).map e
  let : m.IsHaarMeasure := inferInstanceAs ((μ.prod ν).map e).IsHaarMeasure
  let M := multiplicativeTamagawaMeasure F
  let : M.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.1
  let k := Measure.haarScalarFactor M m
  have hm : M = k • m := Measure.isMulLeftInvariant_eq_smul M m
  let c := (ideleClassNormTwist χ s).toMonoidHom.comp (QuotientGroup.mk' _)
  let archChar (u : A) := c (sIdeleInsertion F ∅ u)
  let finiteChar (v : Bf) := c (e (1, v))
  let p (v : Bf) := b (Multiplicative.ofAdd v.val) * finiteChar v
  have he (u : A) : e (u, 1) = sIdeleInsertion F ∅ u := by
    apply Units.ext
    exact Prod.ext (sIdeleInsertion_apply F ∅ u).1.symm (Subtype.ext (funext fun v ↦
      ((sIdeleInsertion_apply F ∅ u).2.2 v (Finset.notMem_empty v)).symm))
  refine ⟨(k : ℂ) * ∫ v, p v ∂ν, fun a ↦ ?_⟩
  let q (u : A) := a (Multiplicative.ofAdd u.val.1) * archChar u
  let f := (adeleSchwartz_inductiveTensor_equiv F).choose (a ⊗ₜ[ℂ] b)
  change (∫ g : I, f (Multiplicative.ofAdd g.val) * c g ∂M) = _
  rw [hm, integral_smul_nnreal_measure]
  change (k : ℂ) * (∫ g : I, f (Multiplicative.ofAdd g.val) * c g
    ∂(μ.prod ν).map e.toHomeomorph.toMeasurableEquiv) = _
  rw [integral_map_equiv]
  have h (x : A × Bf) : f (Multiplicative.ofAdd (e x).val) * c (e x) = q x.1 * p x.2 := by
    have hx : c (e x) = archChar x.1 * finiteChar x.2 := by
      rw [← show e (x.1, 1) * e (1, x.2) = e x by rw [← map_mul]; simp, map_mul, he]
    rw [(adeleSchwartz_inductiveTensor_equiv F).choose_spec a b (e x).val, hx]
    exact mul_mul_mul_comm _ _ _ _
  change (k : ℂ) * (∫ x : A × Bf, f (Multiplicative.ofAdd (e x).val) * c (e x) ∂μ.prod ν) = _
  simp_rw [h]
  rw [integral_prod_mul (μ := μ) (ν := ν) q p]
  exact mul_left_comm _ _ _

/-- Flatness along all coordinate walls makes the archimedean integral entire.
Absolute convergence uses the untwisted local estimate, since the character has norm one. -/
private theorem archNuclearityQuotient_jetEquiv_annihilate_arch
    (χ : U) (a : ℬ(InfiniteAdeleRing F))
    (h : archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces))
    (ha : ∀ x, a (Multiplicative.ofAdd x) = h.val (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) :
    Differentiable ℂ (fun s ↦ ∫ u : (SAdeleRing F ∅)ˣ, a (Multiplicative.ofAdd u.val.1) *
      ideleClassNormTwist χ s (QuotientGroup.mk (sIdeleInsertion F ∅ u))
      ∂sMultiplicativeTamagawaMeasure F ∅) := by
  let S : Finset V := ∅
  let : MeasurableSpace (SAdeleRing F S) := instMeasurableSpaceSAdeleRing F S
  let : BorelSpace (SAdeleRing F S)ˣ := sIdeleGroup_borelSpace
  let r (w : RealPlaces) : {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)} :=
    ⟨InfinitePlace.Completion.ringEquivRealOfIsReal w.2,
    (InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toHomeomorph.isHomeomorph⟩
  let c (w : ComplexPlaces) : {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)} :=
    ⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.2).toHomeomorph.isHomeomorph⟩
  let g : ∀ v : S, ℬ(v.val.adicCompletion F) := fun v ↦ isEmptyElim v
  let t := (sAdeleSchwartz_inductiveTensor_equiv F S).choose (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v))
  have ht (x : SAdeleRing F S) : t (Multiplicative.ofAdd x) = a (Multiplicative.ofAdd x.1) := by
    rw [(sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a g x, Fintype.prod_empty, mul_one]
  have hflat : t ∈ sAdelePolarFree S r c := by
    rw [sAdelePolarFree_eq_span_tmul]
    refine Submodule.subset_span ⟨a, g, ⟨h, fun x ↦ ?_⟩, fun v ↦ isEmptyElim v, rfl⟩
    rw [ha]
    apply congrArg h.val
    refine Prod.ext (funext fun i ↦ ?_) (funext fun j ↦ ?_)
    · change _ = (r i).val (if hw : i.val.IsReal then _ else _)
      simp only [i.2, ↓reduceDIte, RingEquiv.apply_symm_apply]
    · change _ = (c j).val (if hw : j.val.IsReal then _ else _)
      simp only [InfinitePlace.not_isReal_iff_isComplex.mpr j.2, ↓reduceDIte]
      exact ((c j).val.apply_symm_apply _).symm
  let q (u : (SAdeleRing F S)ˣ) : C𝔽 := QuotientGroup.mk (sIdeleInsertion F S u)
  have hq : Continuous q := QuotientGroup.continuous_mk.comp (isClosedEmbedding_sIdeleInsertion F S).continuous
  let n (u : (SAdeleRing F S)ˣ) := ((ideleClassNorm F (q u)).val : ℝ)
  have hn : Continuous n := NNReal.continuous_coe.comp (Units.continuous_val.comp
    ((isProperMap_ideleClassNorm F).continuous.comp hq))
  have hn' (u : (SAdeleRing F S)ˣ) : ((sIdeleQuotientNorm F S (QuotientGroup.mk u)).val : ℝ) = n u := by
    change ((sIdeleQuotientNorm F S _).val : ℝ) = ((ideleNorm F (sIdeleInsertion F S u)).val : ℝ)
    rw [sIdeleQuotientNorm_mk, ideleNorm_sIdeleInsertion]
  let w (u : (SAdeleRing F S)ˣ) := a (Multiplicative.ofAdd u.val.1) * (χ (q u) : ℂ)
  have hw : Continuous w := ((continuous_schwartzBruhat a).comp (continuous_ofAdd.comp
    (continuous_fst.comp Units.continuous_val))).mul (continuous_subtype_val.comp (χ.continuous.comp hq))
  have H := analyticOnNhd_integral_mul_cpow_of_integrable (sMultiplicativeTamagawaMeasure F S)
    w n hn.measurable (fun u ↦ NNReal.coe_pos.mpr (Units.zero_lt _)) isOpen_univ (fun z _ ↦ by
      have hI := sLocalIdelicZFunction_entire_of_polarFree_integrable r c t hflat 1 z
      apply hI.norm.mono' (hw.mul ((Complex.continuous_ofReal.comp hn).cpow continuous_const
        (fun u ↦ Complex.ofReal_mem_slitPlane.mpr (NNReal.coe_pos.mpr (Units.zero_lt _))))).aestronglyMeasurable
      filter_upwards with u
      change ‖w u * _‖ ≤ _
      simp only [w, norm_mul, Circle.norm_coe, mul_one, ht]
      change _ ≤ _ * ‖(1 : ℂ) * ((((sIdeleQuotientNorm F S (QuotientGroup.mk u)).val : ℝ) : ℂ) ^ z)‖
      rw [one_mul, hn']
      exact le_rfl)
  intro z
  change DifferentiableAt ℂ (fun s ↦ ∫ u, a (Multiplicative.ofAdd u.val.1) *
    ((χ (q u) : ℂ) * (n u : ℂ) ^ s) ∂sMultiplicativeTamagawaMeasure F S) z
  simpa only [w, mul_assoc] using (H z (mem_univ z)).differentiableAt

/-- Pair the given finite test with a Gaussian at infinity. Its normalized global zeta
function is entire. Canceling the Gaussian Mellin factor on the right half-plane
therefore gives an entire cofactor of the finite Hecke function for a flat tensor. -/
private theorem archNuclearityQuotient_jetEquiv_annihilate_tensor
    (χ : U) (a : ℬ(InfiniteAdeleRing F)) (b : ℬ(FiniteAdeleRing (𝓞 F) F))
    (h : archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces))
    (ha : ∀ x, a (Multiplicative.ofAdd x) = h.val (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) :
    ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s : {z : ℂ // 1 < z.re},
      globalIdelicZetaIntegral ((adeleSchwartz_inductiveTensor_equiv F).choose (a ⊗ₜ[ℂ] b))
        (ideleClassNormTwist χ s) = u s * finiteHeckeL χ s := by
  let e : Multiplicative (SAdeleRing F ∅) ≃ₜ* Multiplicative (InfiniteAdeleRing F) :=
    ContinuousMulEquiv.mk' (Homeomorph.prodUnique _ (∀ v : (∅ : Finset V), v.val.adicCompletion F))
      (fun _ _ ↦ rfl)
  let : T2Space (Multiplicative (InfiniteAdeleRing F)) :=
    inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing F)) := InfiniteAdeleRing.locallyCompactSpace F
  let : T2Space (Multiplicative (SAdeleRing F ∅)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (SAdeleRing F ∅)) := e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  obtain ⟨G, hG⟩ := exists_archimedeanHeckeTest χ
  obtain ⟨T, hT⟩ := schwartzBruhat_transport e
  let g := (adeleSchwartz_inductiveTensor_equiv F).choose (T G ⊗ₜ[ℂ] b)
  let arch (a : ℬ(InfiniteAdeleRing F)) (z : ℂ) := ∫ u : (SAdeleRing F ∅)ˣ,
    a (Multiplicative.ofAdd u.val.1) * ideleClassNormTwist χ z (QuotientGroup.mk (sIdeleInsertion F ∅ u))
      ∂sMultiplicativeTamagawaMeasure F ∅
  have hΓ (s : {z : ℂ // 1 < z.re}) : arch (T G) s = heckeGammaFactor χ s := by
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)) (hG s)
    apply congrArg (· * _)
    exact (hT G _).trans (congrArg G (e.symm_apply_apply (Multiplicative.ofAdd u.val)))
  let D := (adelicEigendistribution_normalized χ).choose
  let k : ℂ := ((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ)
  have hD := analytic_eval_normalized (adelicEigendistribution_normalized χ).choose_spec.1 g
  have hd : Differentiable ℂ (fun z ↦ D z g) := fun z ↦ (hD z (mem_univ z)).differentiableAt
  refine ⟨fun z ↦ arch a z * (k * D z g),
    (archNuclearityQuotient_jetEquiv_annihilate_arch χ a h ha).mul
      (hd.const_mul k),
    fun s ↦ ?_⟩
  obtain ⟨v, hv⟩ := archNuclearityQuotient_jetEquiv_annihilate_product χ b s
  have h₁ : globalIdelicZetaIntegral g (ideleClassNormTwist χ s) = heckeGammaFactor χ s * v :=
    (hv (T G)).trans (congrArg (· * v) (hΓ s))
  have h₂ := globalIntegral_normalized_ratio χ s.property g
  rw [gaussianCompletedHeckeL_eq_completedHeckeL χ s s.property] at h₂
  have hv' : v = k * D s g * finiteHeckeL χ s := by
    apply mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans s.property))
    refine h₁.symm.trans (h₂.trans ?_)
    change k * (heckeGammaFactor χ s * finiteHeckeL χ s) * D s g = _
    ring
  rw [hv a, hv']
  exact (mul_assoc _ _ _).symm

/-- The half-plane factorization of flat tensors is preserved by finite sums, including
sums for which only the whole representative satisfies the two global polar conditions. -/
private theorem archNuclearityQuotient_jetEquiv_annihilate_flat
    (χ : U) {requireArchMoment : Prop} (f : ℬ(𝔸[F]))
    (hf : f ∈ globalArchimedeanFlatTests F requireArchMoment) :
    ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s : {z : ℂ // 1 < z.re},
      globalIdelicZetaIntegral f (ideleClassNormTwist χ s) = u s * finiteHeckeL χ s := by
  let D := (adelicEigendistribution_normalized χ).choose
  have hlin (s : {z : ℂ // 1 < z.re}) (g : ℬ(𝔸[F])) :
      globalIdelicZetaIntegral g (ideleClassNormTwist χ s) = gaussianCompletedHeckeL χ s * D s g :=
    globalIntegral_normalized_ratio χ s.property g
  induction hf using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨a, b, h, ha, _, rfl⟩ := hx
    exact archNuclearityQuotient_jetEquiv_annihilate_tensor χ a b h ha
  | zero => exact ⟨0, differentiable_const _, fun s ↦ by simp [hlin]⟩
  | add _ _ _ _ h₁ h₂ =>
    obtain ⟨u, hu, huf⟩ := h₁
    obtain ⟨v, hv, hvg⟩ := h₂
    refine ⟨u + v, hu.add hv, fun s ↦ ?_⟩
    rw [hlin, map_add, mul_add, ← hlin, ← hlin, huf, hvg, Pi.add_apply, add_mul]
  | smul c _ _ h₁ =>
    obtain ⟨u, hu, huf⟩ := h₁
    refine ⟨fun z ↦ c * u z, hu.const_mul c, fun s ↦ ?_⟩
    rw [hlin, map_smul, smul_eq_mul, mul_left_comm, ← hlin, huf, mul_assoc]

/-- At a gamma pole the factor regularizing the completed function has order one at
the trivial quasi-character and order zero at all other retained sites. -/
private theorem archNuclearityQuotient_jetEquiv_annihilate_polarOrder
    (χ : U) (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (z : ℂ) (hz : 0 < gammaOrder(χ, z)) :
    analyticOrderAt (spectralFiniteP χ τ hτ) z =
      if ω(χ) = 1 ∧ z = atZeroPole(χ, τ, hτ) then 1 else 0 := by
  let b := ((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℂ) * Complex.I
  have hb : b.re = 0 := by simp [b]
  have hleft : z.re ≤ 0 := by
    by_contra! hpos
    rw [((differentiable_inv_heckeGammaFactor χ).analyticAt z).analyticOrderAt_eq_zero.mpr
      (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hpos))] at hz
    simp at hz
  have hone : 1 - z - b ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.one_re, hb, sub_zero, Complex.zero_re] at hr
    linarith
  have hpole : atZeroPole(χ, τ, hτ) = -b := neg_mul _ _
  rw [hpole]
  by_cases hω : ω(χ) = 1
  · have he : spectralFiniteP χ τ hτ = (fun w ↦ w - -b) * (fun w ↦ 1 - w - b) := by
      funext w
      simp [spectralFiniteP, b, specDenom_hδ' χ hω]
    rw [he, analyticOrderAt_mul (by fun_prop) (by fun_prop),
      (show AnalyticAt ℂ (fun w : ℂ ↦ 1 - w - b) z by fun_prop).analyticOrderAt_eq_zero.mpr hone, add_zero]
    by_cases hz₀ : z = -b
    · rw [hz₀, analyticOrderAt_id_sub_const_self, ite_eq_left ⟨hω, rfl⟩]
    · rw [analyticOrderAt_id_sub_const_of_ne hz₀, ite_eq_right (fun h ↦ hz₀ h.2)]
  · have he : spectralFiniteP χ τ hτ = fun _ ↦ 1 := by
      funext w
      simp [spectralFiniteP, specDenom_hδ χ hω]
    simp [he, hω]

/-- Paper: Equation (7.4.3.13), p. 372.
Each adjusted jet annihilates the archimedean orbital denominator, so the jets are
well defined on the quotient by it. -/
theorem archNuclearityQuotient_jetEquiv_annihilate (j : ArchNuclearityJetIndex χ τ hτ)
    (x : archNuclearityDenominator χ) :
    archNuclearityJet χ τ hτ j x.val = 0 := by
  obtain ⟨f, hf, hx⟩ := (archNuclearityDenominator_mem_restricted χ x.val).mp x.property
  obtain ⟨u, hu, hfactor⟩ := archNuclearityQuotient_jetEquiv_annihilate_flat χ f.val hf
  let φ := (Z(χ, τ, hτ)) x.val
  have hφ : Differentiable ℂ (φ.val : ℂ → ℂ) := fun z ↦
    (φ.property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
  let p := spectralFiniteP χ τ hτ
  let R (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  let Λ₀ := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
  have hp := spectralFiniteP_diff χ τ hτ
  have hR := differentiable_inv_heckeGammaFactor χ
  have hreg : p * (φ.val : ℂ → ℂ) = R * ((Λ₀.val : ℂ → ℂ) * u) := by
    apply eq_of_agree_rightHalf (fun z _ ↦ ((hp.analyticAt z).mul (hφ.analyticAt z)).meromorphicNFAt)
      (fun z _ ↦ ((hR.analyticAt z).mul ((Λ₀.property.analyticAt z).mul (hu.analyticAt z))).meromorphicNFAt) 1
    intro z hz
    have he : φ.val z = u z * finiteHeckeL χ ⟨z, hz⟩ := by
      dsimp only [φ]
      rw [hx, ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f z).2,
        globalIdelicZFunction_eq_integral _ (globalTwist_mem_rightHalf χ hz)]
      exact hfactor ⟨z, hz⟩
    have hg := spectralFiniteG_right χ τ hτ hz
    change R z * Λ₀.val z = p z * finiteHeckeL χ ⟨z, hz⟩ at hg
    change p z * φ.val z = R z * (Λ₀.val z * u z)
    rw [he, ← mul_assoc (R z), hg]
    ring
  let z := j.val.1
  let m := gammaOrder(χ, z)
  let d : ℕ := if ω(χ) = 1 ∧ z = atZeroPole(χ, τ, hτ) then 1 else 0
  have hj : j.val.2 < m - d := j.property
  have hm : 0 < m := by omega
  have hd : analyticOrderAt p z = (d : ℕ∞) := by
    simpa only [d, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
      archNuclearityQuotient_jetEquiv_annihilate_polarOrder χ τ hτ z hm
  have ho := congrArg (fun v : ℂ → ℂ ↦ analyticOrderAt v z) hreg
  rw [analyticOrderAt_mul (hp.analyticAt z) (hφ.analyticAt z),
    analyticOrderAt_mul (hR.analyticAt z) ((Λ₀.property.mul hu).analyticAt z), hd] at ho
  have hbound : (m : ℕ∞) ≤ (d : ℕ∞) + analyticOrderAt (φ.val : ℂ → ℂ) z :=
    (ENat.natCast_toNat_le_self _).trans (le_self_add.trans_eq ho.symm)
  have horder : ((m - d : ℕ) : ℕ∞) ≤ analyticOrderAt (φ.val : ℂ → ℂ) z := by
    cases h : analyticOrderAt (φ.val : ℂ → ℂ) z using ENat.recTopCoe with
    | top => exact le_top
    | coe k =>
      rw [h, ← Nat.cast_add] at hbound
      exact_mod_cast (Nat.sub_le_iff_le_add'.mpr (by exact_mod_cast hbound) : m - d ≤ k)
  unfold archNuclearityJet
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
  change iteratedDeriv j.val.2 (schwartzBergmanEntireInclusion φ).val z = 0
  rw [show ((schwartzBergmanEntireInclusion φ).val : ℂ → ℂ) = φ.val from
    funext (schwartzBergmanEntireInclusion_apply φ)]
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hφ.analyticAt z)).mp horder _ hj

/-- Paper: Equation (7.4.3.13), p. 372.
The adjusted jets assemble into a single continuous linear map from the archimedean
orbital quotient to the product of the coefficient spaces. -/
theorem archNuclearityQuotient_jetEquiv_coefficients :
    ∃ L : ArchNuclearityQuotient χ →L[ℂ] (ArchNuclearityJetIndex χ τ hτ → ℂ),
      ∀ (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ),
        L ((archNuclearityDenominator χ).mkQ x) j = archNuclearityJet χ τ hτ j x := by
  have hker : ∀ j : ArchNuclearityJetIndex χ τ hτ,
      archNuclearityDenominator χ ≤ (archNuclearityJet χ τ hτ j).ker :=
    fun j _ hy ↦ archNuclearityQuotient_jetEquiv_annihilate (χ := χ) (τ := τ) (hτ := hτ) j ⟨_, hy⟩
  refine ⟨ContinuousLinearMap.pi fun j ↦ (archNuclearityDenominator χ).liftQL
    (archNuclearityJet χ τ hτ j) (hker j), ?_⟩
  intro x j
  exact Submodule.liftQ_apply (p := archNuclearityDenominator χ)
    (f := (archNuclearityJet χ τ hτ j).toLinearMap) (h := hker j) (x := x)

/-- Adapted from `globalPrincipalValueConverse_mellin_insertion` in §6.3.
Insertion through the stage agrees with insertion at the chosen finite place. -/
private theorem archNuclearityQuotient_jetEquiv_separating_insertion {T : Finset V}
    (v : T) (x : (v.val.adicCompletion F)ˣ) :
    sIdeleInsertion F T ((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
        ((w : T) → w.val.adicCompletion F)).symm
      (1, ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x))) =
      IdeleGroup.ofAdicCompletion (𝓞 F) F v.val x := by
  classical
  let : DecidableEq T := Classical.decEq _
  let g : (SAdeleRing F T)ˣ := (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) _).symm
    (1, ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x))
  obtain ⟨ha, hf, ho⟩ := sIdeleInsertion_apply F T g
  apply Units.ext
  apply Prod.ext
  · exact ha
  · apply RestrictedProduct.ext
    intro u
    change (sIdeleInsertion F T g).val.2 u =
      RestrictedProduct.mulSingle (fun w : V ↦ w.adicCompletionIntegers F) v.val x.val u
    by_cases hu : u = v.val
    · subst u
      rw [hf v, RestrictedProduct.mulSingle_eq_same]
      change ((Pi.mulSingle (M := fun t : T ↦ (t.val.adicCompletion F)ˣ) v x v :
        (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F) = _
      rw [Pi.mulSingle_eq_same]
    · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hu]
      by_cases hm : u ∈ T
      · rw [hf ⟨u, hm⟩]
        change ((Pi.mulSingle (M := fun t : T ↦ (t.val.adicCompletion F)ˣ) v x ⟨u, hm⟩ :
          (u.adicCompletion F)ˣ) : u.adicCompletion F) = 1
        rw [Pi.mulSingle_eq_of_ne (fun e ↦ hu (congrArg Subtype.val e)), Units.val_one]
      · exact ho u hm

/-- Adapted from `globalPrincipalValueConverse_mellin_factor` in §6.3.
The finite Euler factors in the local and global conventions agree. -/
private theorem archNuclearityQuotient_jetEquiv_separating_factor
    (χ' : U) (v : V) (s : ℂ) :
    finiteLocalEulerFactor v (finitePlaceRestriction F v (ideleClassNormTwist χ' s)) =
      finiteHeckeEulerFactor χ' v s := by
  classical
  let c := finitePlaceRestriction F v (ideleClassNormTwist χ' s)
  let c₀ := finitePlaceRestriction F v (ideleClassNormTwist χ' 0)
  have htwist (x : (v.adicCompletion F)ˣ) :
      c x = c₀ x * (‖x.val‖ : ℂ) ^ s := by
    let g := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v x
    change (χ' g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ s =
      (χ' g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) * _
    rw [Complex.cpow_zero, mul_one, ideleClassNorm_ofAdicCompletion]
    rfl
  have hrestrict (x : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist χ' 0).restrict v x.val = c₀ x := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  have hunram : (∀ u : (v.adicCompletionIntegers F)ˣ,
      c (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) = 1) ↔
        (ideleClassNormTwist χ' 0).IsUnramifiedAt v := by
    rw [HeckeCharacter.isUnramifiedAt_iff]
    refine forall_congr' fun u ↦ ?_
    let x := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u
    change c x = 1 ↔ (ideleClassNormTwist χ' 0).restrict v x.val = 1
    have hn : ‖x.val‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := x)).mp
          ⟨u.val.property, u.inv.property⟩)
    rw [htwist, hn, Complex.ofReal_one, Complex.one_cpow, mul_one, hrestrict]
  change finiteLocalEulerFactor v c = finiteHeckeEulerFactor χ' v s
  by_cases hv : (ideleClassNormTwist χ' 0).IsUnramifiedAt v
  · rw [finiteLocalEulerFactor, ite_eq_left (hunram.mpr hv), finiteHeckeEulerFactor, ite_eq_left hv]
    let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    let hπ := val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
    let π := Units.mk0 _ hπ.ne_zero
    change (1 - c π)⁻¹ = _
    have hn := norm_uniformizer_adicCompletion v π.val hπ
    rw [htwist, hv.localValue_eq π.val hπ, hrestrict, hn,
      Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) s,
      Complex.cpow_neg, Complex.ofReal_natCast]
  · rw [finiteLocalEulerFactor, ite_eq_right (mt hunram.mp hv), finiteHeckeEulerFactor,
      ite_eq_right hv]

/-- Adapted from `globalPrincipalValueConverse_mellin_localFactor` in §6.3.
Restriction to the local stage preserves each selected Euler factor. -/
private theorem archNuclearityQuotient_jetEquiv_separating_localFactor {T : Finset V} (χ : U)
    (hc : ideleClassNormTwist χ 0 ∈ unramifiedOutside F T) (η : PontryaginDual (SIdeleQuotient F T))
    (hχ : sIdeleRestriction F T ⟨ideleClassNormTwist χ 0, hc⟩ =
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η) (v : T) (s : ℂ) :
    let chart := quasiCharacterNormTwist (sIdeleQuotientNorm F T)
      (isProperMap_sIdeleQuotientNorm F T).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η)
    finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chart s)) = finiteHeckeEulerFactor χ v.val s := by
  intro chart
  have htwist (g : (SAdeleRing F T)ˣ) :
      chart s (QuotientGroup.mk g) =
        ideleClassNormTwist χ s (QuotientGroup.mk (sIdeleInsertion F T g)) := by
    have hbase := DFunLike.congr_fun hχ (QuotientGroup.mk g)
    rw [sIdeleRestriction_mk] at hbase
    change (χ (QuotientGroup.mk (sIdeleInsertion F T g)) : ℂ) * _ ^ (0 : ℂ) =
      (η (QuotientGroup.mk g) : ℂ) at hbase
    simp only [Complex.cpow_zero, mul_one] at hbase
    change (η (QuotientGroup.mk g) : ℂ) *
        ((((sIdeleQuotientNorm F T) (QuotientGroup.mk g) : ℝ≥0) : ℝ) : ℂ) ^ s =
      (χ (QuotientGroup.mk (sIdeleInsertion F T g)) : ℂ) * _ ^ s
    rw [← hbase, sIdeleQuotientNorm_mk, ← ideleNorm_sIdeleInsertion]
    rfl
  have hfinite (v : T) : sLocalFiniteRestriction v (chart s) =
      finitePlaceRestriction F v.val (ideleClassNormTwist χ s) := by
    ext1 x
    change chart s (QuotientGroup.mk ((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
        ((w : T) → w.val.adicCompletion F)).symm
      (1, ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x)))) =
      ideleClassNormTwist χ s (QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val x))
    rw [htwist, archNuclearityQuotient_jetEquiv_separating_insertion]
  rw [hfinite, archNuclearityQuotient_jetEquiv_separating_factor]

/-- Removing the finite Euler factors at the stage gives the local principal-value chart.
Multiplying it by the finite Hecke continuation and the outside unit masses recovers
the global transform of every inserted test. -/
private theorem archNuclearityQuotient_jetEquiv_separating_stage (χ : U) (S : Finset V)
    (hS : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hseries : ∀ s : {s : ℂ // 1 < s.re}, L s = finiteHeckeL χ s) :
    ∃ (η : PontryaginDual (SIdeleQuotient F S)) (c : ℂ), c ≠ 0 ∧
      sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hS⟩ =
        (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η ∧
      ∀ f : ℬ(SAdeleRing F S),
        (fun z ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ z))
          =ᶠ[Filter.codiscrete ℂ] fun z ↦ c * sLocalIdelicZFunction
            (sAdelePrincipalValue F (Finset.Subset.refl S) f)
            (quasiCharacterNormTwist (sIdeleQuotientNorm F S)
              (isProperMap_sIdeleQuotientNorm F S).continuous
              ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η) z) * L z := by
  classical
  -- Restrict the unitary character as in §6.3, heckeEulerProductOutside_eq_finite_unitary.
  let unitary := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hS⟩
  have hunitary (x : SIdeleQuotient F S) : ‖unitary x‖ = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [show unitary (QuotientGroup.mk g) = ideleClassNormTwist χ 0
      (QuotientGroup.mk (sIdeleInsertion F S g)) from sIdeleRestriction_mk F S _ g]
    change ‖(χ _ : ℂ) * _ ^ (0 : ℂ)‖ = 1
    simp
  let η : PontryaginDual (SIdeleQuotient F S) :=
    { toFun := fun x ↦ ⟨unitary x, mem_sphere_zero_iff_norm.mpr (hunitary x)⟩
      map_one' := Subtype.ext (map_one unitary)
      map_mul' x y := Subtype.ext (map_mul unitary x y)
      continuous_toFun := unitary.continuous.subtype_mk _ }
  have hb : sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hS⟩ =
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η := rfl
  let c := ∏ᶠ v : {v : V // v ∉ S}, (((finiteLocalMultiplicativeTamagawaMeasure F v.val)
    (v.val.adicCompletionIntegers F).units).toReal : ℂ)
  have hc : c ≠ 0 := by
    apply finprod_ne_zero
    intro v
    rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_ne_zero'.mpr
      (pow_pos (Nat.cast_pos.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v.val))) _)))
  refine ⟨η, c, hc, hb, fun f ↦ ?_⟩
  have hw := weilIdentity_unramifiedOutside_meromorphic S f χ hS L hL fun s hs ↦ hseries ⟨s, hs⟩
  dsimp only at hw
  rw [hb] at hw
  filter_upwards [hw, sLocalIdelicZFunction_principalValue S (Finset.Subset.refl S) f η] with z hz hp
  dsimp only at hp
  rw [hp, hz]
  simp_rw [archNuclearityQuotient_jetEquiv_separating_localFactor χ hS η hb,
    fun v : S ↦ ite_eq_left_iff.mpr (fun h ↦ (h v.property).elim :
      ¬v.val ∈ S → (1 : ℂ) = finiteHeckeEulerFactor χ v.val z)]
  rw [Finset.prod_coe_sort S (fun v ↦ finiteHeckeEulerFactor χ v z),
    div_eq_mul_inv, ← Finset.prod_inv_distrib]
  simp only [mul_assoc, c]

/-- At the exceptional point the simple pole of the completed function accounts
for the one jet omitted from the archimedean multiplicity. -/
private theorem archNuclearityQuotient_jetEquiv_separating_pole (χ : U)
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F)) (hω : ω(χ) = 1) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) atZeroPole(χ, τ, hτ) = -1 := by
  have htriv : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext g
    exact congrArg Subtype.val (DFunLike.congr_fun hω g)
  obtain ⟨t, ⟨hc, hzero, -, -⟩, -⟩ := completedHeckeL_continuation_simplePoles χ _
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2 htriv
  have hphase := existsUnique_ideleNormSection_character_phase χ τ hτ
  have hx : -t = hphase.exists.choose := by
    apply hphase.unique _ hphase.exists.choose_spec
    intro u
    have he := DFunLike.congr_fun hc (QuotientGroup.mk (τ u))
    change (χ (QuotientGroup.mk (τ u)) : ℂ) * _ ^ (0 : ℂ) =
      1 * ((((ideleNorm F (τ u)).val : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ))) at he
    rw [Complex.cpow_zero, mul_one, one_mul, hτ u] at he
    simpa only [Complex.ofReal_neg, neg_mul, mul_comm (t : ℂ) Complex.I] using he
  change meromorphicOrderAt _ (-(hphase.exists.choose : ℂ) * Complex.I) = _
  rwa [← hx, Complex.ofReal_neg, neg_neg, mul_comm (t : ℂ) Complex.I]

/-- An entire global transform with the adjusted vanishing orders has a holomorphic
finite-principal-value chart. On the left half-plane the completed function has no zeros,
and its simple pole on a norm-twist component lowers the required order by one. -/
private theorem archNuclearityQuotient_jetEquiv_separating_analytic (χ : U)
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (u Φ : ℂ → ℂ) (hu : MeromorphicNFOn u univ) (hΦ : Differentiable ℂ Φ)
    (hpos : ∀ z : ℂ, 0 < z.re → 0 ≤ meromorphicOrderAt u z)
    (hjets : ∀ z, (archNuclearityMultiplicity χ τ hτ z : ℕ∞) ≤ analyticOrderAt Φ z)
    (c : ℂ) (hc : c ≠ 0)
    (he : Φ =ᶠ[Filter.codiscrete ℂ] fun z ↦
      c * u z * ((heckeGammaFactor χ z)⁻¹ * continuedCompletedHeckeL χ z)) :
    AnalyticOnNhd ℂ u univ := by
  intro z hz
  apply (hu hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_cases hp : 0 < z.re
  · exact hpos z hp
  let R := fun s ↦ (heckeGammaFactor χ s)⁻¹
  let L := continuedCompletedHeckeL χ
  have hR := (differentiable_inv_heckeGammaFactor χ).analyticAt z
  have hL := (continuedCompletedHeckeL_spec χ).1 hz
  have ho := meromorphicOrderAt_congr (he.filter_mono (nhdsNE_le_codiscrete z))
  change meromorphicOrderAt Φ z = meromorphicOrderAt (((fun _ ↦ c) * u) * (R * L)) z at ho
  rw [meromorphicOrderAt_mul (analyticAt_const.meromorphicAt.mul (hu hz).meromorphicAt)
    (hR.meromorphicAt.mul hL.meromorphicAt), meromorphicOrderAt_mul_of_ne_zero analyticAt_const hc,
    meromorphicOrderAt_mul hR.meromorphicAt hL.meromorphicAt, hR.meromorphicOrderAt_eq,
    (hΦ.analyticAt z).meromorphicOrderAt_eq] at ho
  have hn := hjets z
  have hleft := archJet_completed_order_nonpos χ (le_of_not_gt hp)
  change meromorphicOrderAt L z ≤ 0 at hleft
  cases hU : meromorphicOrderAt u z with
  | top => exact le_top
  | coe k =>
    rw [hU] at ho
    obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) hleft)
    rw [← hl] at ho hleft
    have hl' : l ≤ 0 := by exact_mod_cast hleft
    have hRfin : analyticOrderAt R z ≠ ⊤ := by
      have ha : AnalyticOnNhd ℂ R univ := fun s _ ↦ (differentiable_inv_heckeGammaFactor χ).analyticAt s
      exact fun h ↦ inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (by norm_num : 0 < (1 : ℂ).re))
        (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ hz
          (analyticOrderAt_eq_top.mp h) (mem_univ 1))
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hRfin
    change (r : ℕ∞) = analyticOrderAt (fun s ↦ (heckeGammaFactor χ s)⁻¹) z at hr
    rw [← hr] at ho
    simp only [archNuclearityMultiplicity, ← hr, ENat.toNat_natCast] at hn
    cases hφ : analyticOrderAt Φ z with
    | top =>
      rw [hφ] at ho
      exact ((WithTop.coe_ne_top (a := k + ((r : ℤ) + l))) ho.symm).elim
    | coe n =>
      rw [hφ] at ho hn
      have heq : (n : ℤ) = k + (r + l) := WithTop.coe_inj.mp ho
      by_cases h : ω(χ) = 1 ∧ z = atZeroPole(χ, τ, hτ)
      · have hLpole := archNuclearityQuotient_jetEquiv_separating_pole χ τ hτ h.1
        rw [← h.2] at hLpole
        change meromorphicOrderAt L z = -1 at hLpole
        have hlone : l = -1 := WithTop.coe_inj.mp (hl.trans hLpole)
        have hnr : r - 1 ≤ n := by
          rw [ite_eq_left h] at hn
          exact_mod_cast hn
        exact WithTop.coe_le_coe.mpr (by omega)
      · have hnr : r ≤ n := by
          rw [ite_eq_right h, Nat.sub_zero] at hn
          exact_mod_cast hn
        exact WithTop.coe_le_coe.mpr (by omega)

/-- Inserting a pure local tensor preserves its archimedean factor. A nonzero
value of that factor extracts the inserted finite test by taking an adelic slice. -/
private theorem archNuclearityQuotient_jetEquiv_separating_insert (S : Finset V)
    (a : ℬ(InfiniteAdeleRing F)) (b : ∀ v : S, ℬ(v.val.adicCompletion F))
    (ha : a ∈ archNuclearity_flatFactors) :
    sAdeleSchwartzToGlobal F S ((sAdeleSchwartz_inductiveTensor_equiv F S).choose
      (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, b v))) ∈ globalArchimedeanFlatTests F := by
  classical
  let ins := sAdeleSchwartzToGlobal F S ((sAdeleSchwartz_inductiveTensor_equiv F S).choose
    (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, b v)))
  let k (y : FiniteAdeleRing (𝓞 F) F) := if ∀ v ∉ S, y v ∈ v.adicCompletionIntegers F
    then ∏ v : S, b v (Multiplicative.ofAdd (y v.val)) else 0
  have hv (x : 𝔸[F]) : ins (Multiplicative.ofAdd x) = a (Multiplicative.ofAdd x.1) * k x.2 := by
    dsimp only [ins]
    rw [sAdeleSchwartzToGlobal_apply, (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec]
    dsimp only [k]
    split_ifs
    · rfl
    · exact (mul_zero _).symm
  change ins ∈ _
  by_cases haz : a = 0
  · have hzero : ins = 0 := Subtype.ext (funext fun x ↦ (hv x.toAdd).trans (by
        rw [haz]
        exact zero_mul _))
    rw [hzero]
    exact Submodule.zero_mem _
  obtain ⟨p, hp⟩ : ∃ p : InfiniteAdeleRing F, a (Multiplicative.ofAdd p) ≠ 0 := by
    by_contra! h
    exact haz (Subtype.ext (funext fun x ↦ h x.toAdd))
  let e := (adeleSchwartz_inductiveTensor_equiv F).choose
  have slice (w : InductiveTensor ℬ(InfiniteAdeleRing F) ℬ(FiniteAdeleRing (𝓞 F) F)) :
      ∃ d : ℬ(FiniteAdeleRing (𝓞 F) F), ∀ y, d (Multiplicative.ofAdd y) =
        e w (Multiplicative.ofAdd (p, y)) := by
    induction w using TensorProduct.inductionOn with
    | tmul v d => exact ⟨v (Multiplicative.ofAdd p) • d,
        fun y ↦ ((adeleSchwartz_inductiveTensor_equiv F).choose_spec v d (p, y)).symm⟩
    | add w t hw ht =>
      obtain ⟨d, hd⟩ := hw
      obtain ⟨b, hb⟩ := ht
      exact ⟨d + b, fun y ↦ (congrArg₂ (· + ·) (hd y) (hb y)).trans
        (congrArg (fun q : ℬ(𝔸[F]) ↦ q (Multiplicative.ofAdd (p, y))) (e.map_add w t).symm)⟩
  obtain ⟨d, hd⟩ := slice (e.symm ins)
  rw [e.apply_symm_apply] at hd
  obtain ⟨f₀, hf₀⟩ := ha
  refine Submodule.subset_span ⟨a, (a (Multiplicative.ofAdd p))⁻¹ • d, f₀, hf₀, False.elim, ?_⟩
  apply Subtype.ext
  funext x
  refine ((adeleSchwartz_inductiveTensor_equiv F).choose_spec a _ x.toAdd).trans ?_
  change a (Multiplicative.ofAdd x.toAdd.1) *
    ((a (Multiplicative.ofAdd p))⁻¹ * d (Multiplicative.ofAdd x.toAdd.2)) = _
  change _ = ins (Multiplicative.ofAdd x.toAdd)
  rw [hd x.toAdd.2, hv (p, x.toAdd.2), hv x.toAdd]
  exact congrArg (a (Multiplicative.ofAdd x.toAdd.1) * ·) (inv_mul_cancel_left₀ hp _)

/-- Undoing the finite principal values on a polar-free local test leaves its
archimedean factors flat. The resulting test still has flat archimedean factors
after extension by the integer indicators outside the stage. -/
private theorem archNuclearityQuotient_jetEquiv_separating_lift (S : Finset V)
    (η : PontryaginDual (SIdeleQuotient F S)) (u : ℬ(SAdeleRing F S)) :
    let chart := quasiCharacterNormTwist (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η)
    AnalyticOnNhd ℂ (fun z ↦ sLocalIdelicZFunction u (chart z)) univ →
      ∃ h : ℬ(SAdeleRing F S), (∀ z, sLocalIdelicZFunction u (chart z) =
        sLocalIdelicZFunction (sAdelePrincipalValue F (Finset.Subset.refl S) h) (chart z)) ∧
        sAdeleSchwartzToGlobal F S h ∈ globalArchimedeanFlatTests F := by
  classical
  intro chart hu
  let r (w : RealPlaces) : {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)} :=
    ⟨InfinitePlace.Completion.ringEquivRealOfIsReal w.2,
      (InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toHomeomorph.isHomeomorph⟩
  let c (w : ComplexPlaces) : {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)} :=
    ⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2,
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.2).toHomeomorph.isHomeomorph⟩
  obtain ⟨g, hg⟩ := (sLocalIdelicZFunction_entire_iff_eq_polarFree r c η u).mp hu
  let pv := sAdelePrincipalValue F (Finset.Subset.refl S)
  let A := (globalArchimedeanFlatTests F).comap (sAdeleSchwartzToGlobal F S)
  suffices incl : sAdelePolarFree S r c ≤ A.map pv by
    obtain ⟨h, hh, he⟩ := incl g.property
    exact ⟨h, fun z ↦ (hg z).trans (congrArg (fun q ↦ sLocalIdelicZFunction q (chart z)) he.symm), hh⟩
  rw [sAdelePolarFree_eq_span_tmul]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, b, ⟨f₀, h₀⟩, hb, rfl⟩
  have ha : a ∈ archNuclearity_flatFactors := by
    refine ⟨f₀, fun x ↦ ?_⟩
    let y := InfiniteAdeleRing.ringEquiv_mixedSpace F x
    have he := h₀ y
    refine Eq.trans ?_ he.symm
    apply congrArg (fun t : InfiniteAdeleRing F ↦ a (Multiplicative.ofAdd t))
    funext w
    split_ifs with hw
    · exact ((r ⟨w, hw⟩).val.symm_apply_apply (x w)).symm
    · exact ((c ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩).val.symm_apply_apply (x w)).symm
  choose t ht using fun v ↦ (Set.ext_iff.mp (finitePlacePrincipalValue_range v.val) (b v)).mpr (hb v)
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  refine ⟨e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, t v)), archNuclearityQuotient_jetEquiv_separating_insert S a t ha, ?_⟩
  refine (sAdelePrincipalValue_tmul (Finset.Subset.refl S) a t).trans ?_
  apply congrArg (fun q : ∀ v : S, ℬ(v.val.adicCompletion F) ↦ e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, q v)))
  funext v
  exact (ite_eq_left v.property).trans (ht v)

/-- Unit translates preserve the span of global tensors with flat archimedean factor. -/
private theorem archNuclearityQuotient_jetEquiv_separating_translate
    (w : IdeleGroup (𝓞 F) F) (g : ℬ(𝔸[F])) (hg : g ∈ globalArchimedeanFlatTests F) :
    schwartzBruhatUnitTranslate w g ∈ globalArchimedeanFlatTests F := by
  obtain ⟨u, v, rfl⟩ := archNuclearity_unit_arch_finite w
  refine (show globalArchimedeanFlatTests F ≤ (globalArchimedeanFlatTests F).comap
    (archNuclearity_translateLinear (archNuclearity_archUnit u * archNuclearity_finiteUnit v)) from ?_) hg
  apply Submodule.span_le.mpr
  rintro _ ⟨a, b, f₀, ha, -, rfl⟩
  change schwartzBruhatUnitTranslate (archNuclearity_archUnit u * archNuclearity_finiteUnit v)
    ((adeleSchwartz_inductiveTensor_equiv F).choose (a ⊗ₜ[ℂ] b)) ∈ globalArchimedeanFlatTests F
  rw [archNuclearity_translate_pure]
  obtain ⟨f₁, h₁⟩ := archNuclearity_flatFactors_translate u a ⟨f₀, ha⟩
  exact Submodule.subset_span ⟨_, _, f₁, h₁, False.elim, rfl⟩

/-- Every character with the prescribed norm-one restriction belongs to the given norm chart.
The two characters agree on the kernel, and their quotient on the section is a complex power.
Adapted from the component calculation in §7.2, `sLocalPrincipalValue_chart`. -/
private theorem archNuclearityQuotient_jetEquiv_separating_chart (χ : U)
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (c : QuasiCharacter C𝔽) (hc : ∀ k : (ideleClassNorm F).ker, c k.val = (ω(χ) k : ℂ)) :
    ∃ z : ℂ, ideleClassNormTwist χ z = c := by
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ := q.comp τ
  have hσ : RightInverse σ (ideleClassNorm F) := hτ
  let d := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  obtain ⟨z, hz, -⟩ := existsUnique_complexPower (c.comp σ)
  obtain ⟨w, hw, -⟩ := existsUnique_complexPower (d.comp σ)
  refine ⟨z - w, ContinuousMonoidHom.ext fun g ↦ ?_⟩
  let t := ideleClassNorm F g
  let k : (ideleClassNorm F).ker := ⟨g / σ t, by
    change ideleClassNorm F (g / σ t) = 1
    rw [map_div, hσ]
    exact div_self' _⟩
  have hg : k.val * σ t = g := div_mul_cancel _ _
  let N : ℂ := ((t.val : ℝ) : ℂ)
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr t.ne_zero)
  have hval : d (σ t) * N ^ (z - w) = c (σ t) := by
    rw [show d (σ t) = N ^ w from hw t, show c (σ t) = N ^ z from hz t,
      ← Complex.cpow_add _ _ hN, show w + (z - w) = z by ring]
  change d g * N ^ (z - w) = c g
  calc
    d g * N ^ (z - w) = d k.val * (d (σ t) * N ^ (z - w)) := by rw [← mul_assoc, ← map_mul, hg]
    _ = c g := by rw [hval, ← (show c k.val = d k.val from hc k), ← map_mul, hg]

/-- A flat test with the same Mellin chart as a polar test can be chosen polar.
On the trivial isotype their signed polar values agree. On any other isotype
a normalized difference of norm-one translates kills both polar values. -/
private theorem archNuclearityQuotient_jetEquiv_separating_polar (χ : U)
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (f : P) (g : ℬ(𝔸[F])) (hg : g ∈ globalArchimedeanFlatTests F)
    (he : ∀ z, globalIdelicZFunction g (ideleClassNormTwist χ z) =
      globalIdelicZFunction f.val (ideleClassNormTwist χ z)) :
    mkΘ(χ, f) ∈ archNuclearityDenominator χ := by
  apply (mem_archNuclearityDenominator_iff_flatPolarImage χ _).mpr
  have hcomp (c : QuasiCharacter C𝔽) (hc : ∀ k : (ideleClassNorm F).ker, c k.val = (ω(χ) k : ℂ)) :
      globalIdelicZFunction g c = globalIdelicZFunction f.val c := by
    obtain ⟨z, rfl⟩ := archNuclearityQuotient_jetEquiv_separating_chart χ τ hτ c hc
    exact he z
  let M := globalIdelicMellin (F := F)
  have mk (b : P) (hb : ∀ (c : {c : QuasiCharacter C𝔽 // 0 ≤ globalIdelicOrderBound c}),
      (∀ k : (ideleClassNorm F).ker, c.val k.val = (ω(χ) k : ℂ)) →
      (M b.val).val c = (M g).val c) : mkΘ(χ, f) = mkΘ(χ, b) := by
    apply (Submodule.Quotient.eq (Π(χ))).mpr
    change f.val - b.val ∈ (homogeneousAdelicThetaLinearMap F (ω(χ))).ker
    apply (mem_homogeneousAdelicTheta_ker_iff (ω(χ)) _).mpr
    intro c hc
    rw [map_sub]
    change (M f.val).val c - (M b.val).val c = 0
    exact sub_eq_zero.mpr ((hcomp c.val hc).symm.trans (hb c hc).symm)
  by_cases hω : ω(χ) = 1
  · have htriv (s : ℂ) : globalIdelicZFunction g (ideleClassNormTwist (1 : U) s) =
        globalIdelicZFunction f.val (ideleClassNormTwist (1 : U) s) :=
      hcomp _ fun k ↦ (normOneRestriction_unitaryChart (ideleClassNorm F)
        (isProperMap_ideleClassNorm F).continuous (1 : U) s k).trans (by rw [hω]; rfl)
    have hzero := tendsto_nhds_unique ((globalIdelicZFunction_residue_zero g).congr
      (fun s ↦ congrArg (s * ·) (htriv s))) (globalIdelicZFunction_residue_zero f.val)
    have hone := tendsto_nhds_unique ((globalIdelicZFunction_residue_one g).congr
      (fun s ↦ congrArg ((s - 1) * ·) (htriv s))) (globalIdelicZFunction_residue_one f.val)
    have hmass : ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ) ≠ 0 := by
      let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
      let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
        (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
      exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
        ⟨(Measure.measure_univ_pos.mpr (NeZero.ne _)).ne', isCompact_univ.measure_ne_top⟩)
    obtain ⟨h₀, h₁⟩ := (mem_adelePolarSubspace _).mp f.property
    have hpol : g ∈ P := (mem_adelePolarSubspace g).mpr
      ⟨(mul_left_cancel₀ (neg_ne_zero.mpr hmass) hzero).trans h₀,
       (mul_left_cancel₀ hmass hone).trans h₁⟩
    exact ⟨⟨g, hpol⟩, hg, mk _ fun _ _ ↦ rfl⟩
  · obtain ⟨h, hh⟩ : ∃ h : (ideleClassNorm F).ker, (ω(χ) h : ℂ) ≠ 1 :=
      not_forall.mp fun hall ↦ hω (PontryaginDual.ext fun u ↦ Subtype.ext (hall u))
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective h.val
    have hw1 : ideleNorm F w = 1 := by
      change ideleClassNorm F (QuotientGroup.mk w) = 1
      rw [hw, MonoidHom.mem_ker.mp h.property]
    let c := (ω(χ) h : ℂ) - 1
    let b := c⁻¹ • (schwartzBruhatUnitTranslate w g - g)
    have hb : b ∈ P := by
      have hp : adelePolarValues (schwartzBruhatUnitTranslate w g) = adelePolarValues g := by
        apply Prod.ext
        · change g (Multiplicative.ofAdd (w.inv * 0)) = g (Multiplicative.ofAdd 0)
          rw [mul_zero]
        · have hd := archNuclearity_hatC_translate w g
          change (adelePolarValues (schwartzBruhatUnitTranslate w g)).2 =
            ((((ideleNorm F w).val : ℝ) : ℂ) * (adelePolarValues g).2) at hd
          simpa only [hw1, Units.val_one, NNReal.coe_one, Complex.ofReal_one, one_mul] using hd
      change (adelePolarValues (F := F)) (c⁻¹ • (schwartzBruhatUnitTranslate w g - g)) = 0
      rw [map_smul, map_sub]
      change c⁻¹ • (adelePolarValues (schwartzBruhatUnitTranslate w g) - adelePolarValues g) = 0
      rw [hp, sub_self, smul_zero]
    refine ⟨⟨b, hb⟩, (globalArchimedeanFlatTests F).smul_mem _
      ((globalArchimedeanFlatTests F).sub_mem
        (archNuclearityQuotient_jetEquiv_separating_translate w g hg) hg), mk _ ?_⟩
    intro z hz
    change (M (c⁻¹ • (schwartzBruhatUnitTranslate w g - g))).val z = _
    rw [map_smul, map_sub]
    change c⁻¹ * ((M (schwartzBruhatUnitTranslate w g)).val z - (M g).val z) = (M g).val z
    rw [show (M (schwartzBruhatUnitTranslate w g)).val z = _ from globalIdelicMellin_unitTranslate w g z,
      hw, hz h, show (ω(χ) h : ℂ) * (M g).val z - (M g).val z = c * (M g).val z by
        rw [show c = _ from rfl, sub_mul, one_mul]]
    exact inv_mul_cancel_left₀ (sub_ne_zero.mpr hh) _

/-- On a finite stage containing the ramification, vanishing of the adjusted global
jets removes every pole of the local principal-value chart. Replace that chart by
a polar-free local test, then undo the finite principal values before insertion. -/
private theorem archNuclearityQuotient_jetEquiv_separating_at_stage (χ : U)
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (S : Finset V) (hS : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (a : ℬ(SAdeleRing F S)) (f : P) (hf : sAdeleSchwartzToGlobal F S a = f.val)
    (hjets : ∀ z, (archNuclearityMultiplicity χ τ hτ z : ℕ∞) ≤
      analyticOrderAt (fun s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s)) z) :
    mkΘ(χ, f) ∈ archNuclearityDenominator χ := by
  let R (s : ℂ) := (heckeGammaFactor χ s)⁻¹
  let Λ := continuedCompletedHeckeL χ
  let L := toMeromorphicNFOn (R * Λ) univ
  have hΛ := (continuedCompletedHeckeL_spec χ).1
  have hR := differentiable_inv_heckeGammaFactor χ
  have hm : MeromorphicOn (R * Λ) univ := fun s hs ↦
    ((hR.analyticAt s).meromorphicAt.mul (hΛ hs).meromorphicAt)
  have hseries (s : {s : ℂ // 1 < s.re}) : L s = finiteHeckeL χ s := by
    have hn := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans s.property)
    have hnf : MeromorphicNFAt (R * Λ) s :=
      (meromorphicNFAt_mul_iff_right (hR.analyticAt _) (inv_ne_zero hn)).mpr (hΛ (mem_univ _))
    rw [show L s = _ from toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ s.val),
      toMeromorphicNFAt_eq_self.mpr hnf]
    change (heckeGammaFactor χ s)⁻¹ * continuedCompletedHeckeL χ s = _
    rw [(continuedCompletedHeckeL_spec χ).2 s]
    exact inv_mul_cancel_left₀ hn _
  obtain ⟨η, c, hc, hη, hstage⟩ := archNuclearityQuotient_jetEquiv_separating_stage χ S
    hS L (meromorphicNFOn_toMeromorphicNFOn _ _) hseries
  let chart := quasiCharacterNormTwist (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous
    ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η)
  let pv := sAdelePrincipalValue F (Finset.Subset.refl S)
  let u (z : ℂ) := sLocalIdelicZFunction (pv a) (chart z)
  have hu : MeromorphicNFOn u univ := sLocalIdelicZFunction_meromorphic (pv a) η
  have hpos (z : ℂ) (hz : 0 < z.re) : 0 ≤ meromorphicOrderAt u z := by
    have hbound := sLocalIdelicZFunction_principalValue_pole_bound a η z
    rw [← archNuclearityGammaOrder_eq_sLocal χ S η hS hη z,
      ((hR.analyticAt z).analyticOrderAt_eq_zero.mpr
        (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hz)))] at hbound
    simpa only [ENat.toNat_zero, Nat.cast_zero, neg_zero, WithTop.coe_zero] using hbound
  have hfac := hstage a
  rw [hf] at hfac
  have hd := globalIdelicZFunction_entire_of_vanishing f.val f.property χ
  have han : AnalyticOnNhd ℂ u univ := by
    apply archNuclearityQuotient_jetEquiv_separating_analytic χ τ hτ u _ hu hd hpos hjets c hc
    have hL : R * Λ =ᶠ[Filter.codiscrete ℂ] L := toMeromorphicNFOn_eqOn_codiscrete hm
    filter_upwards [hfac, hL] with s hs hLs
    exact hs.trans (congrArg (c * u s * ·) hLs.symm)
  obtain ⟨b, hb, hflat⟩ := archNuclearityQuotient_jetEquiv_separating_lift S η (pv a) han
  apply archNuclearityQuotient_jetEquiv_separating_polar χ τ hτ f (sAdeleSchwartzToGlobal F S b) hflat
  have eqZ : (fun z ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S b) (ideleClassNormTwist χ z))
      =ᶠ[Filter.codiscrete ℂ] fun z ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ z) := by
    filter_upwards [hstage b, hfac] with z hz hz'
    change _ = c * sLocalIdelicZFunction (pv b) (chart z) * L z at hz
    rw [← hb z] at hz
    exact hz.trans hz'.symm
  intro z
  exact (((globalIdelicZFunction_meromorphic _ χ (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (globalIdelicZFunction_meromorphic f.val χ (mem_univ z))).mp
    (eqZ.filter_mono (nhdsNE_le_codiscrete z))).eq_of_nhds

/-- Paper: Equation (7.4.3.13), p. 372.
The adjusted jets separate the classes of the archimedean orbital quotient: a class
on which every jet vanishes is the class of a flat test, that is, it lies in the
denominator. -/
theorem archNuclearityQuotient_jetEquiv_separating (x : Θ₀(χ))
    (hx : ∀ j, archNuclearityJet χ τ hτ j x = 0) : x ∈ archNuclearityDenominator χ := by
  classical
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (Π(χ)) x
  obtain ⟨A, a, ha⟩ := sAdeleSchwartzToGlobal_exhaustive F f.val
  obtain ⟨T, hT⟩ : ∃ T : Finset V, ideleClassNormTwist χ 0 ∈ unramifiedOutside F T := by
    apply Set.mem_iUnion.mp
    rw [iUnion_unramifiedOutside]
    trivial
  let S := A ∪ T
  have hAS : A ⊆ S := Finset.subset_union_left
  have hS : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S := fun v hv ↦
    hT v (fun h ↦ hv (Finset.mem_union_right _ h))
  apply archNuclearityQuotient_jetEquiv_separating_at_stage χ τ hτ S hS
    (sAdeleSchwartzTransition F hAS a) f ((LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F hAS) a).trans ha)
  intro z
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    ((globalIdelicZFunction_entire_of_vanishing f.val f.property χ).analyticAt z)).mpr
  intro k hk
  let j : ArchNuclearityJetIndex χ τ hτ := ⟨(z, k), hk⟩
  exact (archNuclearityJet_apply χ τ hτ j f).2.2.1.symm.trans (hx j)

/-- Entire divisibility is equivalent to the corresponding pointwise inequalities of vanishing orders. -/
private theorem archNuclearityMellin_range_entire_dvd
    (g f : entireContinuousMapSubalgebra) :
    g ∣ f ↔ ∀ z : ℂ, analyticOrderAt (g.val : ℂ → ℂ) z ≤
      analyticOrderAt (f.val : ℂ → ℂ) z := by
  have ha (a : entireContinuousMapSubalgebra) (z : ℂ) : AnalyticAt ℂ (a.val : ℂ → ℂ) z :=
    (show Differentiable ℂ a.val from a.property).analyticAt z
  constructor
  · rintro ⟨k, rfl⟩ z
    change _ ≤ analyticOrderAt ((g.val : ℂ → ℂ) * (k.val : ℂ → ℂ)) z
    rw [analyticOrderAt_mul (ha g z) (ha k z)]
    exact self_le_add_right _ _
  · intro hord
    let q := (f.val : ℂ → ℂ) / (g.val : ℂ → ℂ)
    have hq : MeromorphicOn q univ := fun z _ ↦ (ha f z).meromorphicAt.div (ha g z).meromorphicAt
    have hdiff : Differentiable ℂ (toMeromorphicNFOn q univ) := by
      intro z
      apply AnalyticAt.differentiableAt
      have hnf := meromorphicNFOn_toMeromorphicNFOn q univ (mem_univ z)
      apply hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [meromorphicOrderAt_toMeromorphicNFOn hq (mem_univ z),
        meromorphicOrderAt_div (ha f z).meromorphicAt (ha g z).meromorphicAt,
        (ha f z).meromorphicOrderAt_eq, (ha g z).meromorphicOrderAt_eq]
      have hle := hord z
      generalize analyticOrderAt (f.val : ℂ → ℂ) z = m at hle ⊢
      generalize analyticOrderAt (g.val : ℂ → ℂ) z = n at hle ⊢
      cases m using ENat.recTopCoe with
      | top => simp
      | coe m =>
        cases n using ENat.recTopCoe with
        | top => simp at hle
        | coe n =>
          exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr (by exact_mod_cast hle : (n : ℤ) ≤ m))
    refine ⟨⟨⟨_, hdiff.continuous⟩, hdiff⟩, Subtype.ext (ContinuousMap.ext fun z ↦ ?_)⟩
    change f.val z = g.val z * toMeromorphicNFOn q univ z
    by_cases hz : g.val z = 0
    · have hpos := lt_of_lt_of_le (pos_iff_ne_zero.mpr ((ha g z).analyticOrderAt_ne_zero.mpr hz))
          (hord z)
      rw [hz, zero_mul]
      exact (ha f z).analyticOrderAt_ne_zero.mp hpos.ne'
    · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hq (mem_univ z),
        toMeromorphicNFAt_eq_self.mpr ((ha f z).div (ha g z) hz).meromorphicNFAt]
      exact (mul_div_cancel₀ _ hz).symm

/-- A maximum of vanishing orders identifies an entire divisibility condition with an ideal and additional jets. -/
private theorem archNuclearityMellin_range_ideal_intersection
    (g h : entireContinuousMapSubalgebra) (m : ℂ → ℕ)
    (horder : ∀ z : ℂ, analyticOrderAt (h.val : ℂ → ℂ) z =
      max (analyticOrderAt (g.val : ℂ → ℂ) z) (m z : ℕ∞))
    (φ : SchwartzBergman (univ : Set ℝ)) :
    φ ∈ schwartzBergmanDivisible h ↔
      φ ∈ schwartzBergmanDivisible g ∧
        ∀ z : ℂ, ∀ k : ℕ, k < m z → iteratedDeriv k (φ.val : ℂ → ℂ) z = 0 := by
  have hval : ((schwartzBergmanEntireInclusion φ).val : ℂ → ℂ) = φ.val :=
    funext (schwartzBergmanEntireInclusion_apply φ)
  have hφdiff : Differentiable ℂ (φ.val : ℂ → ℂ) := fun z ↦
    (φ.property.2.1 z (mem_univ _)).differentiableAt
      (Filter.univ_mem' fun _ ↦ mem_univ _)
  have hmem (g : entireContinuousMapSubalgebra) :
      φ ∈ schwartzBergmanDivisible g ↔
        ∀ z : ℂ, analyticOrderAt (g.val : ℂ → ℂ) z ≤
          analyticOrderAt (φ.val : ℂ → ℂ) z := by
    change schwartzBergmanEntireInclusion φ ∈ Ideal.span ({g} : Set entireContinuousMapSubalgebra) ↔ _
    rw [Ideal.mem_span_singleton, archNuclearityMellin_range_entire_dvd]
    simp only [hval]
  rw [hmem h, hmem g]
  simp_rw [horder, max_le_iff]
  rw [forall_and]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro z
  exact natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hφdiff.analyticAt z)

/-- Separated zero sets in the two half-planes turn the generator product into a maximum of vanishing orders. -/
private theorem archNuclearityMellin_range_max_order
    (g h r : ℂ → ℂ) (hg : Differentiable ℂ g) (hh : Differentiable ℂ h)
    (hr : Differentiable ℂ r) (b : ℂ) (hb : b.re = 0) (δ : ℕ)
    (hδ : δ = 0 ∨ δ = 1)
    (he : ∀ z : ℂ, (z + b) ^ δ * h z = (-1 : ℂ) ^ δ * (g z * r z))
    (hgleft : ∀ z : ℂ, z.re ≤ 0 → g z ≠ 0)
    (hrright : ∀ z : ℂ, 0 < z.re → r z ≠ 0) (z : ℂ) :
    analyticOrderAt h z = max (analyticOrderAt g z)
      (((analyticOrderAt r z).toNat - if δ = 1 ∧ z = -b then 1 else 0 : ℕ) : ℕ∞) := by
  classical
  have har : AnalyticOnNhd ℂ r Set.univ := fun w _ ↦ hr.analyticAt w
  have hrone : analyticOrderAt r 1 = 0 :=
    (hr.analyticAt 1).analyticOrderAt_eq_zero.mpr (hrright 1 (by norm_num))
  have hrfinite : analyticOrderAt r z ≠ ⊤ :=
    har.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 1)
      (Set.mem_univ z) (by rw [hrone]; simp)
  let p : ℂ → ℂ := fun w ↦ (w + b) ^ δ
  have hp : Differentiable ℂ p := (differentiable_id.add_const b).pow δ
  have hfunc : p * h = (fun _ ↦ (-1 : ℂ) ^ δ) * (g * r) := funext he
  have ho := congrArg (fun f : ℂ → ℂ ↦ analyticOrderAt f z) hfunc
  rw [analyticOrderAt_mul (hp.analyticAt z) (hh.analyticAt z),
    analyticOrderAt_const_mul ((hg.analyticAt z).mul (hr.analyticAt z))
      ((-1 : ℂ) ^ δ), ite_eq_right (pow_ne_zero δ (by norm_num : (-1 : ℂ) ≠ 0)),
    analyticOrderAt_mul (hg.analyticAt z) (hr.analyticAt z)] at ho
  have hporder : analyticOrderAt p z = if z = -b then (δ : ℕ∞) else 0 := by
    by_cases hz : z = -b
    · subst z
      have hlinear : analyticOrderAt (fun w : ℂ ↦ w + b) (-b) = 1 := by
        simpa only [sub_neg_eq_add] using
          (analyticOrderAt_id_sub_const_self (c := -b) :
            analyticOrderAt (fun w : ℂ ↦ w - -b) (-b) = 1)
      change analyticOrderAt ((fun w : ℂ ↦ w + b) ^ δ) (-b) = _
      rw [analyticOrderAt_pow (show AnalyticAt ℂ (fun w : ℂ ↦ w + b) (-b) by fun_prop), hlinear]
      simp
    · rw [ite_eq_right hz]
      apply (hp.analyticAt z).analyticOrderAt_eq_zero.mpr
      apply pow_ne_zero
      intro heq
      exact hz (eq_neg_of_add_eq_zero_left heq)
  rw [hporder] at ho
  by_cases hpos : 0 < z.re
  · have hz : z ≠ -b := by
      intro heq
      have hzre := congrArg Complex.re heq
      simp only [Complex.neg_re, hb, neg_zero] at hzre
      linarith
    have hrzero : analyticOrderAt r z = 0 :=
      (hr.analyticAt z).analyticOrderAt_eq_zero.mpr (hrright z hpos)
    have horder : analyticOrderAt h z = analyticOrderAt g z := by simpa [hz, hrzero] using ho
    simpa [hrzero] using horder
  · have hgz : analyticOrderAt g z = 0 :=
      (hg.analyticAt z).analyticOrderAt_eq_zero.mpr (hgleft z (le_of_not_gt hpos))
    rw [hgz, zero_add] at ho
    rw [hgz, max_eq_right (by positivity)]
    cases hRz : analyticOrderAt r z using ENat.recTopCoe with
    | top => exact (hrfinite hRz).elim
    | coe m =>
      cases hHz : analyticOrderAt h z using ENat.recTopCoe with
      | top => simp [hHz, hRz] at ho
      | coe n =>
        rw [hHz, hRz] at ho
        rcases hδ with rfl | rfl
        · simpa using ho
        · by_cases hz : z = -b
          · have hnatcast : ((1 + n : ℕ) : ℕ∞) = (m : ℕ∞) := by
              simpa [hz, Nat.cast_add] using ho
            have hn : 1 + n = m := by exact_mod_cast hnatcast
            simpa [hz] using (show (n : ℕ∞) = ((m - 1 : ℕ) : ℕ∞) from
              by exact_mod_cast (show n = m - 1 by omega))
          · simpa [hz] using ho

/-- The functional equation and the zero-free right boundary exclude completed zeros in the closed left half-plane. -/
private theorem archNuclearityMellin_range_completed_order_left
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (s : ℂ) (hs : s.re ≤ 0) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) s ≤ 0 := by
  obtain ⟨ε, hε, hne, he⟩ := completedHeckeL_continuation_functionalEquation χ
    (continuedCompletedHeckeL χ) (continuedCompletedHeckeL χ⁻¹)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
  let r (z : ℂ) := 1 - z
  have hr : HasDerivAt r (-1) s := by simpa [r] using (hasDerivAt_id s).const_sub 1
  have e : continuedCompletedHeckeL χ⁻¹ ∘ r = fun z ↦ ε z * continuedCompletedHeckeL χ z :=
    funext he
  have ho := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹)
    (show AnalyticAt ℂ r s by dsimp [r]; fun_prop) (hr.deriv.trans_ne (by norm_num))
  rw [e] at ho
  change meromorphicOrderAt (ε * continuedCompletedHeckeL χ) s = _ at ho
  rw [meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt s) (hne s)] at ho
  rw [ho]
  apply le_of_not_gt
  intro hz
  have hzre := completedHeckeL_continuation_zeros χ⁻¹ (continuedCompletedHeckeL χ⁻¹)
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
    (s := r s) (by change 0 < 1 - s.re; linarith) hz
  change 1 - s.re < 1 at hzre
  linarith

/-- After removing the two poles, the completed generator is nonzero in the closed left half-plane. -/
private theorem archNuclearityMellin_range_completed_ne_zero_left
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (s : ℂ) (hs : s.re ≤ 0) :
    (regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2).val s ≠ 0 := by
  classical
  let L := continuedCompletedHeckeL χ
  let G := regularizedCompletedHeckeL χ τ hτ L
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
  let x : ℝ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let b : ℂ := (x : ℂ) * Complex.I
  let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
  let p : ℂ → ℂ := fun z ↦ (z + b) ^ δ * (1 - z - b) ^ δ
  have hG : Differentiable ℂ (G.val : ℂ → ℂ) := G.property
  have hp : Differentiable ℂ p := by dsimp [p]; fun_prop
  have hL := (continuedCompletedHeckeL_spec χ).1
  by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · by_cases hs₀ : s = -b
    · subst s
      exact (regularizedCompletedHeckeL_ne_zero_at_canceled_poles χ τ hτ L
        (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2 hχ).1
    · have hp₀ : p s ≠ 0 := by
        simp only [p, δ, ite_eq_left hχ, pow_one]
        apply mul_ne_zero
        · intro h
          exact hs₀ (eq_neg_of_add_eq_zero_left h)
        · intro h
          have hreal := congrArg Complex.re h
          simp only [Complex.sub_re, Complex.one_re, Complex.zero_re,
            b, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, zero_mul, sub_self] at hreal
          linarith
      have hm : MeromorphicOn (p * L) univ := fun z _ ↦
        (hp.analyticAt z).meromorphicAt.mul (hL (mem_univ z)).meromorphicAt
      have hord : meromorphicOrderAt (G.val : ℂ → ℂ) s = meromorphicOrderAt L s := by
        change meromorphicOrderAt (toMeromorphicNFOn (p * L) univ) s = _
        rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ s),
          meromorphicOrderAt_mul_of_ne_zero (hp.analyticAt s) hp₀]
      apply (hG.analyticAt s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
      apply le_antisymm
      · rw [hord]
        exact archNuclearityMellin_range_completed_order_left F χ s hs
      · exact (hG.analyticAt s).meromorphicOrderAt_nonneg
  · have he : (G.val : ℂ → ℂ) = L := by
      change toMeromorphicNFOn (fun z ↦ (z + b) ^ δ * (1 - z - b) ^ δ * L z) univ = L
      simp only [δ, ite_eq_right hχ, pow_zero, one_mul]
      exact toMeromorphicNFOn_eq_self.mpr hL
    apply (hG.analyticAt s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
    apply le_antisymm
    · rw [he]
      exact archNuclearityMellin_range_completed_order_left F χ s hs
    · exact (hG.analyticAt s).meromorphicOrderAt_nonneg


/-- The finite and completed regularized generators differ by the reciprocal gamma factor and one linear factor. -/
private theorem archNuclearityMellin_range_generator_identity
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F)) :
    let x := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
    let b := (x : ℂ) * Complex.I
    let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
    let H := archRegularizedFiniteHeckeL χ τ hτ
    let G := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    ∀ z : ℂ, (z + b) ^ δ * H.val z =
      (-1 : ℂ) ^ δ * G.val z * (heckeGammaFactor χ z)⁻¹ := by
  classical
  intro x b δ H G
  let p : ℂ → ℂ := fun z ↦ (z + b) ^ δ * (1 - z - b) ^ δ
  let L := continuedCompletedHeckeL χ
  have hp : Differentiable ℂ p := by dsimp [p]; fun_prop
  have hL := (continuedCompletedHeckeL_spec χ).1
  have hm : MeromorphicOn (p * L) univ := fun z _ ↦
    (hp.analyticAt z).meromorphicAt.mul (hL (mem_univ z)).meromorphicAt
  have hb : b.re = 0 := by simp [b]
  have hδ : (if (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)) = 1 then (1 : ℕ) else 0) = δ := by
    by_cases hω : (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)) = 1
    · simp [δ, hω, specDenom_hδ' χ hω]
    · simp [δ, hω, specDenom_hδ χ hω]
  have hGval (z : ℂ) (hz : 1 < z.re) :
      G.val z = p z * completedHeckeL χ ⟨z, hz⟩ := by
    have hpne : p z ≠ 0 := by
      apply mul_ne_zero <;> apply pow_ne_zero <;> intro he
      · have := congrArg Complex.re he
        simp only [Complex.add_re, hb, add_zero, Complex.zero_re] at this
        linarith
      · have := congrArg Complex.re he
        simp only [Complex.sub_re, Complex.one_re, hb, sub_zero, Complex.zero_re] at this
        linarith
    have hnf : MeromorphicNFAt (p * L) z :=
      (meromorphicNFAt_mul_iff_right (hp.analyticAt z) hpne).2 (hL (mem_univ z))
    change toMeromorphicNFOn (p * L) univ z = p z * completedHeckeL χ ⟨z, hz⟩
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ z),
      toMeromorphicNFAt_eq_self.mpr hnf]
    exact congrArg (p z * ·) ((continuedCompletedHeckeL_spec χ).2 ⟨z, hz⟩)
  have hHval (z : ℂ) (hz : 1 < z.re) :
      H.val z = (z - 1 + b) ^ δ * finiteHeckeL χ ⟨z, hz⟩ := by
    have h := archRegularizedFiniteHeckeL_apply χ τ hτ ⟨z, hz⟩
    change H.val z = (z - 1 - (-(x : ℂ) * Complex.I)) ^
      (if (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)) = 1 then 1 else 0) * finiteHeckeL χ ⟨z, hz⟩ at h
    rw [neg_mul, sub_neg_eq_add, hδ] at h
    exact h
  have hleft : Differentiable ℂ (fun z : ℂ ↦ (z + b) ^ δ * H.val z) :=
    ((differentiable_id.add_const b).pow δ).mul H.property
  have hright : Differentiable ℂ (fun z : ℂ ↦
      (-1 : ℂ) ^ δ * G.val z * (heckeGammaFactor χ z)⁻¹) :=
    ((G.property.const_mul _).mul (differentiable_inv_heckeGammaFactor χ))
  have hnear : (fun z : ℂ ↦ (z + b) ^ δ * H.val z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ ↦ (-1 : ℂ) ^ δ * G.val z * (heckeGammaFactor χ z)⁻¹) := by
    have hU : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (show IsOpen {z : ℂ | 1 < z.re} from
        isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hU] with z hz
    rw [hHval z hz, hGval z hz]
    change (z + b) ^ δ * ((z - 1 + b) ^ δ * finiteHeckeL χ ⟨z, hz⟩) =
      (-1 : ℂ) ^ δ * ((z + b) ^ δ * (1 - z - b) ^ δ *
        (heckeGammaFactor χ z * finiteHeckeL χ ⟨z, hz⟩)) * (heckeGammaFactor χ z)⁻¹
    rw [show z - 1 + b = (-1 : ℂ) * (1 - z - b) by ring, mul_pow]
    have hne := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)
    field_simp [hne]
  have hA : AnalyticOnNhd ℂ (fun z : ℂ ↦ (z + b) ^ δ * H.val z) univ :=
    fun z _ ↦ hleft.analyticAt z
  have hB : AnalyticOnNhd ℂ (fun z : ℂ ↦
      (-1 : ℂ) ^ δ * G.val z * (heckeGammaFactor χ z)⁻¹) univ :=
    fun z _ ↦ hright.analyticAt z
  exact congrFun (hA.eq_of_eventuallyEq hB hnear)

/-- The finite generator has the completed vanishing orders together with the adjusted archimedean multiplicities. -/
private theorem archNuclearityMellin_range_orders
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F)) :
    ∀ z : ℂ, analyticOrderAt ((archRegularizedFiniteHeckeL χ τ hτ).val : ℂ → ℂ) z =
      max (analyticOrderAt ((regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
        (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2).val : ℂ → ℂ) z)
        (archNuclearityMultiplicity χ τ hτ z : ℕ∞) := by
  classical
  let x : ℝ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let b : ℂ := (x : ℂ) * Complex.I
  let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
  let H := archRegularizedFiniteHeckeL χ τ hτ
  let G := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
  have hb : b.re = 0 := by simp [b]
  have hδ : δ = 0 ∨ δ = 1 := by dsimp [δ]; split_ifs <;> simp
  have hδone : δ = 1 ↔ (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)) = 1 := by
    by_cases hω : (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)) = 1
    · simp [δ, hω, specDenom_hδ' χ hω]
    · simp [δ, hω, specDenom_hδ χ hω]
  have hpole : (-(((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℝ) : ℂ) * Complex.I) = -b := by simp only [b, x, neg_mul]
  intro z
  have h := archNuclearityMellin_range_max_order (G.val : ℂ → ℂ) (H.val : ℂ → ℂ)
    (fun z ↦ (heckeGammaFactor χ z)⁻¹) G.property H.property
    (differentiable_inv_heckeGammaFactor χ) b hb δ hδ
    (fun z ↦ (archNuclearityMellin_range_generator_identity F χ τ hτ z).trans
      (mul_assoc _ _ _))
    (fun z hz ↦ archNuclearityMellin_range_completed_ne_zero_left F χ τ hτ z hz)
    (fun z hz ↦ inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hz)) z
  have hmult : archNuclearityMultiplicity χ τ hτ z =
      (analyticOrderAt (fun w ↦ (heckeGammaFactor χ w)⁻¹) z).toNat -
        if δ = 1 ∧ z = -b then 1 else 0 := by
    simp only [archNuclearityMultiplicity, hpole, hδone]
  rw [hmult]
  exact h

/-- Paper: Theorem 7.4.3.1(4), p. 368.
The Mellin image of the flat denominator is the intersection of the entire
principal ideal generated by the regularized finite Hecke function with the
Schwartz–Bergman space. That image is closed. -/
theorem archNuclearityMellin_range :
    let D := (Z(χ, τ, hτ)) '' (archNuclearityDenominator χ : Set (Θ₀(χ)))
    D = (schwartzBergmanDivisible (archRegularizedFiniteHeckeL χ τ hτ) : Set B) ∧ IsClosed D := by
  classical
  let P₀ := adelePolarSubspace F
  let ω := (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F))
  let K := LinearMap.ker ((homogeneousAdelicThetaLinearMap F ω).domRestrict P₀)
  let E := ↥P₀ ⧸ K
  let Z := (exists_globalPolarThetaMellin χ τ hτ).choose
  let G := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
  let H := archRegularizedFiniteHeckeL χ τ hτ
  let : PolynormableSpace ℂ (E) := polynormableSpace_quotient (K)
  have hD (x : E) : x ∈ archNuclearityDenominator χ ↔
      ∀ j : ArchNuclearityJetIndex χ τ hτ, archNuclearityJet χ τ hτ j x = 0 :=
    ⟨fun hx j ↦ archNuclearityQuotient_jetEquiv_annihilate
        (χ := χ) (τ := τ) (hτ := hτ) j ⟨x, hx⟩,
      fun hx ↦ archNuclearityQuotient_jetEquiv_separating
        (χ := χ) (τ := τ) (hτ := hτ) x hx⟩
  have hjet (x : E) (j : ArchNuclearityJetIndex χ τ hτ) :
      archNuclearityJet χ τ hτ j x =
        iteratedDeriv j.val.2 (Z x).val j.val.1 := by
    unfold archNuclearityJet
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
    exact congrArg (fun f : ℂ → ℂ ↦ iteratedDeriv j.val.2 f j.val.1)
      (funext (schwartzBergmanEntireInclusion_apply (Z x)))
  have hD0 : spectralNuclearityDenominator χ τ hτ 0 = schwartzBergmanDivisible G := by
    unfold spectralNuclearityDenominator
    apply congrArg schwartzBergmanDivisible
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    change G.val (z + (0 : ℂ)) = G.val z
    simp only [add_zero]
  have hZrange (φ : SchwartzBergman (univ : Set ℝ)) :
      (∃ x : E, Z x = φ) ↔ φ ∈ schwartzBergmanDivisible G := by
    change φ ∈ Z.toLinearMap.range ↔ φ ∈ schwartzBergmanDivisible G
    rw [← spectralNuclearityDenominator_zero χ τ hτ, hD0]
  have horder := archNuclearityMellin_range_orders F χ τ hτ
  have hideal (φ : SchwartzBergman (univ : Set ℝ)) : φ ∈ schwartzBergmanDivisible H ↔
      φ ∈ schwartzBergmanDivisible G ∧ ∀ z k,
        k < archNuclearityMultiplicity χ τ hτ z → iteratedDeriv k φ.val z = 0 :=
    archNuclearityMellin_range_ideal_intersection G H (archNuclearityMultiplicity χ τ hτ)
      horder φ
  have heq : Z '' (archNuclearityDenominator χ : Set (E)) =
      (schwartzBergmanDivisible H : Set (SchwartzBergman (univ : Set ℝ))) := by
    ext φ
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply (hideal _).mpr
      refine ⟨(hZrange _).mp ⟨x, rfl⟩, fun z k hk ↦ ?_⟩
      exact (hjet x ⟨(z, k), hk⟩).symm.trans ((hD x).mp hx ⟨(z, k), hk⟩)
    · intro hφ
      obtain ⟨hrange, hjets⟩ := (hideal φ).mp hφ
      obtain ⟨x, hx⟩ := (hZrange φ).mpr hrange
      refine ⟨x, (hD x).mpr ?_, hx⟩
      intro j
      rw [hjet x j, hx]
      exact hjets j.val.1 j.val.2 j.property
  exact ⟨heq, heq.symm ▸ schwartzBergmanDivisible_isClosed H⟩

/-- Paper: Equation (7.4.3.13), p. 372.
Every family of coefficient values is realized by a class of the archimedean
orbital quotient: the coefficient map is onto the whole product. -/
theorem archNuclearityQuotient_jetEquiv_realization
    (y : ArchNuclearityJetIndex χ τ hτ → ℂ) :
    ∃ x : Θ₀(χ), ∀ j, archNuclearityJet χ τ hτ j x = y j := by
  obtain ⟨x, hx⟩ := archJet_surjective χ τ hτ y
  exact ⟨x, congrFun hx⟩

/-- A continuous bijection from a quotient of a closed part of a strict LF-space onto
a countable product of scalar lines is open. Intersect each Fréchet stage with the closed
part to obtain the increasing family of images used by the open mapping theorem. -/
private theorem archNuclearityQuotient_jetEquiv_inverse_continuous_open
    {A Y ι : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [ContinuousSMul ℂ A] [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y] [Countable ι]
    (hA : IsStrictLFSpace A) (B₀ : Submodule ℂ A) (hB : IsClosed (B₀ : Set A))
    (q : B₀ →L[ℂ] Y) (hq : Surjective q) (T : Y →L[ℂ] (ι → ℂ)) (hT : Bijective T) :
    IsOpenMap T := by
  let : T2Space Y := T2Space.of_injective_continuous hT.1 T.continuous
  obtain ⟨_, stage, hmono, hV, hcover, _⟩ := hA
  let slice (n : ℕ) := B₀.comap (stage n).subtype
  let j (n : ℕ) : slice n →L[ℂ] B₀ :=
    ((stage n).subtypeL.comp (slice n).subtypeL).codRestrict B₀ (fun z ↦ z.property)
  have hW (n : ℕ) : IsFrechetTVS (slice n) := by
    obtain ⟨hadd, hpoly, hmet, hcomp⟩ := hV n
    let : UniformSpace (stage n) := IsTopologicalAddGroup.rightUniformSpace _
    let : IsUniformAddGroup (stage n) := isUniformAddGroup_of_addCommGroup
    let : CompleteSpace (stage n) := hcomp
    have hc : IsClosed (slice n : Set (stage n)) := hB.preimage continuous_subtype_val
    let : UniformSpace (slice n) := UniformSpace.comap Subtype.val inferInstance
    let : IsUniformAddGroup (slice n) := (slice n).toAddSubgroup.isUniformAddGroup
    let : TopologicalSpace.MetrizableSpace (slice n) := IsEmbedding.subtypeVal.metrizableSpace
    let : CompleteSpace (slice n) := hc.completeSpace_coe
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  have hPi : IsFrechetTVS (ι → ℂ) := by
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  apply isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hPi) hW
    (fun n ↦ q.comp (j n)) _ _ T hT.2
  · rintro n _ ⟨y, rfl⟩
    exact ⟨⟨⟨y.val.val, hmono (Nat.le_succ n) y.val.property⟩, y.property⟩, rfl⟩
  · intro x
    obtain ⟨y, rfl⟩ := hq x
    obtain ⟨n, hn⟩ := hcover y.val
    exact ⟨n, ⟨⟨⟨y.val, hn⟩, y.property⟩, rfl⟩⟩

/-- Paper: Equation (7.4.3.13), p. 372.
The coefficient map of the archimedean orbital quotient is a topological isomorphism:
the inverse of the bijective coefficient map is continuous. -/
theorem archNuclearityQuotient_jetEquiv_inverse_continuous
    (L : ArchNuclearityQuotient χ →L[ℂ] (ArchNuclearityJetIndex χ τ hτ → ℂ))
    (hL : ∀ (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ),
      L ((archNuclearityDenominator χ).mkQ x) j = archNuclearityJet χ τ hτ j x)
    (h : Function.Bijective L) :
    Continuous ((LinearEquiv.ofBijective L.toLinearMap h).symm :
      (ArchNuclearityJetIndex χ τ hτ → ℂ) → ArchNuclearityQuotient χ) := by
  -- Openness follows from the LF structure for any coordinate map with this bijectivity.
  have _ := hL
  obtain ⟨e⟩ := archNuclearityJet_basis_index_equiv χ τ hτ
  let : Countable (ArchNuclearityJetIndex χ τ hτ) := e.symm.injective.countable
  let q : P →L[ℂ] ArchNuclearityQuotient χ :=
    (archNuclearityDenominator χ).mkQL.comp (Π(χ)).mkQL
  have hq : Surjective q :=
    (archNuclearityDenominator χ).mkQ_surjective.comp (Π(χ)).mkQ_surjective
  have hopen := archNuclearityQuotient_jetEquiv_inverse_continuous_open
    (adeleSchwartz_strictLF (F := F)).2 P (adelePolarSubspace_closed (F := F)) q hq L h
  exact (LinearEquiv.ofBijective L.toLinearMap h).toEquiv.continuous_symm_iff.mpr hopen

/-- Paper: Equation (7.4.3.13) and the following paragraph, p. 372.
The coefficients of a quotient class are its adjusted jets, with the product topology.
The map includes simultaneous realization of every family of coefficients. -/
theorem archNuclearityQuotient_jetEquiv :
    ∃ e : ArchNuclearityQuotient χ ≃L[ℂ] (ArchNuclearityJetIndex χ τ hτ → ℂ),
      ∀ (x : Θ₀(χ)) j, e ((archNuclearityDenominator χ).mkQ x) j =
        archNuclearityJet χ τ hτ j x := by
  obtain ⟨L, hL⟩ := archNuclearityQuotient_jetEquiv_coefficients (χ := χ) (τ := τ) (hτ := hτ)
  have hinj : Function.Injective L := by
    intro a b hab
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (archNuclearityDenominator χ) a
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (archNuclearityDenominator χ) b
    have hzero : x - y ∈ archNuclearityDenominator χ := by
      refine archNuclearityQuotient_jetEquiv_separating (χ := χ) (τ := τ) (hτ := hτ)
        (x - y) fun j ↦ ?_
      rw [map_sub, ← hL x j, ← hL y j]
      exact sub_eq_zero.mpr (congrArg (fun f : (ArchNuclearityJetIndex χ τ hτ → ℂ) ↦ f j) hab)
    have hsub : (archNuclearityDenominator χ).mkQ x - (archNuclearityDenominator χ).mkQ y = 0 := by
      rw [← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hzero
    exact sub_eq_zero.mp hsub
  have hsurj : Function.Surjective L := by
    intro y
    obtain ⟨x, hx⟩ := archNuclearityQuotient_jetEquiv_realization (χ := χ) (τ := τ) (hτ := hτ) y
    exact ⟨(archNuclearityDenominator χ).mkQ x, funext fun j ↦ (hL x j).trans (hx j)⟩
  refine ⟨⟨LinearEquiv.ofBijective L.toLinearMap ⟨hinj, hsurj⟩, L.continuous, ?_⟩, hL⟩
  exact archNuclearityQuotient_jetEquiv_inverse_continuous (χ := χ) (τ := τ) (hτ := hτ)
    L hL ⟨hinj, hsurj⟩

/-- A continuous linear functional on a product of copies of `ℂ` depends on only finitely
many coordinates: the preimage of the unit ball contains a box that is unrestricted outside a
finite set of coordinates. -/
private theorem archNuclearityJet_span_finiteCoordinates {J : Type*} [DecidableEq J]
    (g : (J → ℂ) →L[ℂ] ℂ) :
    ∃ I : Finset J, ∀ y : J → ℂ, g y = ∑ i ∈ I, y i * g (Pi.single i 1) := by
  have h0 : (g : (J → ℂ) → ℂ) ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : J → ℂ) :=
    g.continuous.continuousAt.preimage_mem_nhds
      (by simpa using Metric.ball_mem_nhds (0 : ℂ) one_pos)
  rw [nhds_pi, Filter.mem_pi'] at h0
  obtain ⟨I, t, ht, hsub⟩ := h0
  refine ⟨I, fun y ↦ ?_⟩
  set r : J → ℂ := y - ∑ i ∈ I, y i • Pi.single i 1 with hr
  have hrI : ∀ i ∈ I, r i = 0 := by
    intro i hi
    simp [hr, Finset.sum_apply, Pi.single_apply, hi]
  have hgr : g r = 0 := by
    by_contra hne
    have hmem : (2 / g r) • r ∈ (I : Set J).pi t := by
      intro i hi
      simp only [Pi.smul_apply, hrI i hi, smul_zero]
      exact mem_of_mem_nhds (ht i)
    have := hsub hmem
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, map_smul, smul_eq_mul] at this
    rw [div_mul_cancel₀ _ hne] at this
    norm_num at this
  have hy : y = r + ∑ i ∈ I, y i • Pi.single i 1 := by simp [hr]
  conv_lhs => rw [hy]
  rw [map_add, hgr, zero_add, map_sum]
  simp [map_smul]

/-- If the quotient by `D` is identified with the product of copies of `ℂ` indexed by `J`,
with coordinates the functionals `jet j`, then the closed span of the `jet j` in the strong
dual is the annihilator of `D`. -/
private theorem archNuclearityJet_span_of_equiv {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (D : Submodule ℂ E) {J : Type*} (jet : J → StrongDual ℂ E)
    (e : (E ⧸ D) ≃L[ℂ] (J → ℂ)) (he : ∀ x j, e (D.mkQ x) j = jet j x) :
    ((Submodule.span ℂ (Set.range jet)).topologicalClosure : Set (StrongDual ℂ E)) =
      {ℓ | ∀ x : D, ℓ x.val = 0} := by
  classical
  apply Set.Subset.antisymm
  · let A : Submodule ℂ (StrongDual ℂ E) :=
      { carrier := {ℓ | ∀ x : D, ℓ x.val = 0}
        add_mem' := fun ha hb x ↦ by simp [ha x, hb x]
        zero_mem' := fun x ↦ rfl
        smul_mem' := fun c ℓ hℓ x ↦ by simp [hℓ x] }
    have hA : IsClosed (A : Set (StrongDual ℂ E)) := by
      have : (A : Set (StrongDual ℂ E)) = ⋂ x : D, {ℓ | ℓ x.val = 0} := by
        ext ℓ; simp [A]
      rw [this]
      exact isClosed_iInter fun x ↦ isClosed_eq (continuous_eval_const _) continuous_const
    have hle : Submodule.span ℂ (Set.range jet) ≤ A := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩ x
      rw [← he, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero D).mpr x.property, map_zero,
        Pi.zero_apply]
    exact Submodule.topologicalClosure_minimal _ hle hA
  · intro ℓ hℓ
    apply Submodule.le_topologicalClosure
    have hker : D ≤ LinearMap.ker ℓ.toLinearMap := fun x hx ↦ hℓ ⟨x, hx⟩
    let l₀ : (E ⧸ D) →ₗ[ℂ] ℂ := D.liftQ ℓ.toLinearMap hker
    have hl₀ : Continuous l₀ :=
      (Submodule.isQuotientMap_mkQ D).continuous_iff.mpr ℓ.continuous
    let g : (J → ℂ) →L[ℂ] ℂ :=
      (⟨l₀, hl₀⟩ : (E ⧸ D) →L[ℂ] ℂ).comp e.symm.toContinuousLinearMap
    obtain ⟨I, hI⟩ := archNuclearityJet_span_finiteCoordinates g
    have hℓeq : ℓ = ∑ i ∈ I, g (Pi.single i 1) • jet i := by
      ext x
      have h1 : ℓ x = g (e (D.mkQ x)) := by
        simp [g, l₀]
      rw [h1, hI]
      simp only [he, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
        smul_eq_mul, mul_comm]
    rw [hℓeq]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Paper: Theorem 7.4.3.1(2), p. 368.
The closure of the linear span of the jets in the strong dual is the annihilator
of the archimedean-flat image. -/
theorem archNuclearityJet_span :
    ((Submodule.span ℂ (Set.range (archNuclearityJet χ τ hτ))).topologicalClosure :
        Set (StrongDual ℂ (Θ₀(χ)))) =
      {ℓ | ∀ x : archNuclearityDenominator χ, ℓ x.val = 0} :=
  Exists.elim (archNuclearityQuotient_jetEquiv χ τ hτ) fun e he ↦
    archNuclearityJet_span_of_equiv (archNuclearityDenominator χ) (archNuclearityJet χ τ hτ) e he

/-- Transport the topology generated by all seminorms across a continuous linear equivalence. -/
private theorem archNuclearityStrongDual_finest_of_equiv {A E : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (e : FinestLocallyConvex A ≃L[ℂ] E) :
    (inferInstance : TopologicalSpace E) = (inferInstance : TopologicalSpace (FinestLocallyConvex E)) := by
  let := finestLocallyConvex_t2 A
  let := finestLocallyConvex_t2 E
  have h := continuous_of_finestLocallyConvex A
    (show FinestLocallyConvex A →ₗ[ℂ] FinestLocallyConvex E from e.toLinearMap)
  have h' := continuous_of_finestLocallyConvex E
    (show FinestLocallyConvex E →ₗ[ℂ] FinestLocallyConvex A from e.symm.toLinearMap)
  apply le_antisymm <;> apply continuous_id_iff_le.mp
  · exact (h.comp e.symm.continuous).congr (fun x ↦ e.apply_symm_apply x)
  · exact (e.continuous.comp h').congr (fun x ↦ e.apply_symm_apply x)

/-- Paper: Theorem 7.4.3.1(3), p. 368.
For a fixed enumeration of the adjusted jets, the descended jets form a Schauder basis
of the strong dual of the archimedean quotient, with continuous coefficient functionals
on that strong dual. Pullback along the quotient map recovers the original jets.
Under the quotient's jet-coordinate equivalence, the basis consists of the coordinate
projections. Its coefficient functionals evaluate at the corresponding unit vectors.
Each dual vector is already recovered by a finite coordinate truncation. -/
private theorem archNuclearityJet_basis_schauder
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (σ : ℕ ≃ ArchNuclearityJetIndex χ τ hτ) :
    ∃ (d : ℕ → StrongDual ℂ (ArchNuclearityQuotient χ))
      (b : ℕ → StrongDual ℂ (StrongDual ℂ (ArchNuclearityQuotient χ))),
      (∀ n x, d n ((archNuclearityDenominator χ).mkQ x) = archNuclearityJet χ τ hτ (σ n) x) ∧
        IsSchauderBasis d b := by
  classical
  obtain ⟨e, he⟩ := archNuclearityQuotient_jetEquiv χ τ hτ
  let d (n : ℕ) : StrongDual ℂ (ArchNuclearityQuotient χ) :=
    (ContinuousLinearMap.proj (σ n)).comp e.toContinuousLinearMap
  let v (n : ℕ) : ArchNuclearityQuotient χ := e.symm (Pi.single (σ n) 1)
  let b (n : ℕ) : StrongDual ℂ (StrongDual ℂ (ArchNuclearityQuotient χ)) :=
    ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (v n)
  refine ⟨d, b, fun n x ↦ he x (σ n), ⟨fun m n ↦ ?_, fun ℓ ↦ ?_⟩⟩
  · change e (e.symm (Pi.single (σ m) 1)) (σ n) = if m = n then 1 else 0
    rw [e.apply_symm_apply, Pi.single_apply]
    by_cases hmn : m = n
    · subst n
      simp
    · simp [hmn, show σ n ≠ σ m from fun h ↦ hmn (σ.injective h).symm]
  · let L := ℓ.comp e.symm.toContinuousLinearMap
    -- Adapted from sLocalGammaOrbitalQuotient_dual_basis_finite in Sec3b:
    -- continuity in the product topology gives a finite set of coordinates
    -- on which the functional depends.
    have hU : L ⁻¹' Metric.ball 0 1 ∈ 𝓝 0 :=
      L.continuous.continuousAt.preimage_mem_nhds (by
        rw [map_zero]
        exact Metric.ball_mem_nhds 0 one_pos)
    rw [nhds_pi, Filter.mem_pi'] at hU
    obtain ⟨T, neighborhoods, hU, hsub⟩ := hU
    have hzero (y : ArchNuclearityJetIndex χ τ hτ → ℂ) (hy : ∀ i ∈ T, y i = 0) :
        L y = 0 := by
      by_contra hne
      have hval : L ((2 / L y) • y) = 2 := by
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne]
      have hmem : (2 / L y) • y ∈ Set.pi (↑T) neighborhoods := fun i hi ↦ by
        rw [Pi.smul_apply, hy i hi, smul_zero]
        exact mem_of_mem_nhds (hU i)
      have hball := hsub hmem
      rw [Set.mem_preimage, hval, Metric.mem_ball, dist_zero_right] at hball
      norm_num at hball
    let K := (T.image σ.symm).sup id + 1
    unfold HasSum
    rw [SummationFilter.conditional_filter_eq_map_range, Filter.tendsto_map'_iff]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop K] with k hk
    symm
    change ∑ m ∈ Finset.range k, b m ℓ • d m = ℓ
    ext q
    have hvan := hzero (e q - ∑ m ∈ Finset.range k, e q (σ m) • Pi.single (σ m) (1 : ℂ))
      fun j hj ↦ by
        have hjk : σ.symm j ∈ Finset.range k := by
          have hjle := Finset.le_sup (f := id) (Finset.mem_image_of_mem σ.symm hj)
          exact Finset.mem_range.mpr (by dsimp [K, id] at hk hjle; omega)
        simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
        rw [Finset.sum_eq_single_of_mem (σ.symm j) hjk]
        · simp
        · intro m _ hm
          have hne : j ≠ σ m := fun h ↦ hm (by rw [h, σ.symm_apply_apply])
          simp [hne]
    simp only [map_sub, map_sum, map_smul, sub_eq_zero] at hvan
    change ℓ (e.symm (e q)) = ∑ m ∈ Finset.range k, e q (σ m) • ℓ (v m) at hvan
    rw [e.symm_apply_apply] at hvan
    simpa [b, d, mul_comm] using hvan.symm

/-- Paper: Theorem 7.4.3.1(3), p. 368.
Every enumeration of the adjusted jets gives a Schauder basis on the quotient strong
dual. Pullback along the quotient map recovers the original jets. -/
theorem archNuclearityJet_basis :
    let Q := ArchNuclearityQuotient χ
    let J := ArchNuclearityJetIndex χ τ hτ
    Nonempty (ℕ ≃ J) ∧
      ∀ σ : ℕ ≃ J, ∃ (d : ℕ → StrongDual ℂ Q) (b : ℕ → StrongDual ℂ (StrongDual ℂ Q)),
        (∀ n x, d n ((archNuclearityDenominator χ).mkQ x) = archNuclearityJet χ τ hτ (σ n) x) ∧
        IsSchauderBasis d b :=
  ⟨archNuclearityJet_basis_index_equiv χ τ hτ, archNuclearityJet_basis_schauder χ τ hτ⟩

/-- Enumerating the adjusted jets identifies the quotient with the space of complex sequences. -/
private theorem archNuclearityStrongDual_finest_sequenceEquiv
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    Nonempty (ArchNuclearityQuotient χ ≃L[ℂ] (ℕ → ℂ)) := by
  let τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F :=
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleNorm F) := canonicalIdeleNormSection_rightInverse F
  obtain ⟨q, _⟩ := archNuclearityQuotient_jetEquiv χ τ hτ
  obtain ⟨σ⟩ := (archNuclearityJet_basis χ τ hτ).1
  exact ⟨q.trans (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : ℕ ↦ ℂ) σ.symm)⟩

/-- Paper: Theorem 7.4.3.1(1), p. 368.
The archimedean-flat theta image is closed in the zero-moment theta space, because
`archNuclearityQuotient_jetEquiv` identifies the quotient by it with a product of
copies of `ℂ`, which is Hausdorff, and the quotient map is continuous. -/
private theorem archNuclearityDenominator_isClosed_jetEquiv
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F)) :
    IsClosed (archNuclearityDenominator χ : Set (Θ₀(χ))) := by
  obtain ⟨e, -⟩ := archNuclearityQuotient_jetEquiv (χ := χ) (τ := τ) (hτ := hτ)
  have h : (archNuclearityDenominator χ : Set (Θ₀(χ))) =
      (fun x ↦ e (Submodule.mkQ (archNuclearityDenominator χ) x)) ⁻¹'
        {(0 : ArchNuclearityJetIndex χ τ hτ → ℂ)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have h0 (y : ArchNuclearityQuotient χ) : e y = 0 ↔ y = 0 := by
      rw [← map_zero e]
      exact e.injective.eq_iff
    exact ⟨fun hx ↦ (h0 _).mpr ((Submodule.Quotient.mk_eq_zero _).mpr hx),
      fun hx ↦ (Submodule.Quotient.mk_eq_zero _).mp ((h0 _).mp hx)⟩
  rw [h]
  exact isClosed_singleton.preimage
    (e.continuous.comp (Submodule.continuous_mkQ (archNuclearityDenominator χ)))

/-- Smooth compactly supported cut-offs away from the coordinate walls of a mixed real and
complex coordinate space that are eventually one at every point off the walls. -/
private theorem archNuclearityDenominator_ne_bot_cutoff (ι κ : Type*) [Fintype ι] [Fintype κ] :
    ∃ k : ℕ → ((ι → ℝ) × (κ → ℂ)) → ℝ,
      (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (k n)) ∧
      (∀ n, HasCompactSupport (k n)) ∧
      (∀ n, Disjoint (tsupport (k n)) {x | (∃ i, x.1 i = 0) ∨ ∃ j, x.2 j = 0}) ∧
      (∀ n x, 0 ≤ k n x ∧ k n x ≤ 1) ∧
      (∀ x, ¬((∃ i, x.1 i = 0) ∨ ∃ j, x.2 j = 0) →
        ∀ᶠ n in Filter.atTop, k n x = 1) := by
  let W : Set ((ι → ℝ) × (κ → ℂ)) := {x | (∃ i, x.1 i = 0) ∨ ∃ j, x.2 j = 0}
  have hW : IsClosed W := by
    have hWe : W = (⋃ i, {x : (ι → ℝ) × (κ → ℂ) | x.1 i = 0}) ∪
        ⋃ j, {x : (ι → ℝ) × (κ → ℂ) | x.2 j = 0} := by
      ext x
      constructor
      · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
        · exact Or.inl (mem_iUnion.mpr ⟨i, hi⟩)
        · exact Or.inr (mem_iUnion.mpr ⟨j, hj⟩)
      · rintro (h | h)
        · exact Or.inl (mem_iUnion.mp h)
        · exact Or.inr (mem_iUnion.mp h)
    rw [hWe]
    exact (isClosed_iUnion_of_finite fun i ↦ isClosed_eq (by fun_prop) continuous_const).union
      (isClosed_iUnion_of_finite fun j ↦ isClosed_eq (by fun_prop) continuous_const)
  obtain ⟨f, hfs, hfc, hfr⟩ := hW.isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  have hf0 (x : (ι → ℝ) × (κ → ℂ)) : 0 ≤ f x := (hfr ⟨x, rfl⟩).1
  let b (n : ℕ) : ContDiffBump (0 : (ι → ℝ) × (κ → ℂ)) :=
    ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  refine ⟨fun n x ↦ Real.smoothTransition (n * f x - 1) * b n x, fun n ↦ ?_, fun n ↦ ?_,
    fun n ↦ ?_, fun n x ↦ ?_, fun x hx ↦ ?_⟩
  · exact (Real.smoothTransition.contDiff.comp ((contDiff_const.mul hfc).sub contDiff_const)).mul
      (b n).contDiff
  · exact (b n).hasCompactSupport.mul_left
  · have hcl : IsClosed {x : (ι → ℝ) × (κ → ℂ) | 1 ≤ n * f x} :=
      isClosed_le continuous_const (continuous_const.mul hfc.continuous)
    have hsub : tsupport (fun x ↦ Real.smoothTransition (n * f x - 1) * b n x) ⊆
        {x : (ι → ℝ) × (κ → ℂ) | 1 ≤ n * f x} := by
      refine closure_minimal (fun x hx ↦ ?_) hcl
      by_contra hlt
      have hlt' : n * f x < 1 := not_le.mp hlt
      exact hx (mul_eq_zero_of_left
        (Real.smoothTransition.zero_of_nonpos (by linarith)) _)
    rw [Set.disjoint_left]
    intro x hx hw
    have h1 : 1 ≤ n * f x := hsub hx
    have h0 : f x = 0 := by
      have hn : x ∉ Function.support f := by
        rw [hfs]
        exact fun h ↦ h hw
      exact Function.notMem_support.mp hn
    rw [h0, mul_zero] at h1
    linarith
  · exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (b n).nonneg,
      (mul_le_mul (Real.smoothTransition.le_one _) (b n).le_one (b n).nonneg
        zero_le_one).trans_eq (one_mul 1)⟩
  · have hmem : x ∈ Function.support f := by
      rw [hfs]
      exact hx
    have hpos : 0 < f x := lt_of_le_of_ne (hf0 x) (Ne.symm hmem)
    obtain ⟨N, hN⟩ := exists_nat_ge (max (2 / f x) ‖x‖)
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hn' : max (2 / f x) ‖x‖ ≤ n := hN.trans (by exact_mod_cast hn)
    have h1 : 1 ≤ n * f x - 1 := by
      have h2 := (div_le_iff₀ hpos).mp ((le_max_left _ _).trans hn')
      linarith
    have h2 : x ∈ Metric.closedBall (0 : (ι → ℝ) × (κ → ℂ)) (b n).rIn := by
      rw [mem_closedBall_zero_iff]
      exact ((le_max_right _ _).trans hn').trans (le_add_of_nonneg_right zero_le_one)
    change Real.smoothTransition (n * f x - 1) * b n x = 1
    rw [Real.smoothTransition.one_of_one_le h1, (b n).one_of_mem_closedBall h2, mul_one]

/-- If an integrable function has zero integral against every member of a sequence of
cut-offs with values in the unit interval that is eventually one at each point, then its
integral is zero. -/
private theorem archNuclearityDenominator_ne_bot_limit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : X → ℂ) (hG : Integrable G μ) (k : ℕ → X → ℝ)
    (hk : ∀ n x, 0 ≤ k n x ∧ k n x ≤ 1) (hlim : ∀ x, ∀ᶠ n in Filter.atTop, k n x = 1)
    (hint : ∀ n, Integrable (fun x ↦ (k n x : ℂ) * G x) μ)
    (h0 : ∀ n, ∫ x, (k n x : ℂ) * G x ∂μ = 0) : ∫ x, G x ∂μ = 0 := by
  have h := tendsto_integral_of_dominated_convergence (fun x ↦ ‖G x‖)
    (fun n ↦ (hint n).aestronglyMeasurable) hG.norm
    (fun n ↦ ae_of_all _ fun x ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hk n x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hk n x).2)
    (ae_of_all _ fun x ↦ tendsto_nhds_of_eventually_eq
      ((hlim x).mono fun n hn ↦ by rw [hn, Complex.ofReal_one, one_mul]))
  simp only [h0] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- A norm twist of a unitary character whose exponent has real part greater than one lies in
the half-plane of absolute convergence of the zeta integral. -/
private theorem archNuclearityDenominator_ne_bot_rightHalf
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (s : ℂ) (hs : 1 < s.re) :
    ideleClassNormTwist χ s ∈
      (relativeRightHalfPlane (ideleClassNorm F) (isProperMap_ideleClassNorm F)
        (ideleClassNorm_ne_one (F := F)) 1 : Set (HeckeCharacter (𝓞 F) F)) :=
  show 1 < quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F)) (ideleClassNormTwist χ s) from
    (quasiCharacterAbscissa_ideleClassNormTwist χ s).symm ▸ hs

/-- Some adelic test has a nonzero zeta integral at the square of the norm twist. -/
private theorem archNuclearityDenominator_ne_bot_zeta_ne_zero
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    ∃ f : ℬ(𝔸[F]), globalIdelicZetaIntegral f (ideleClassNormTwist χ 2) ≠ 0 := by
  have hs : (2 : ℂ) ∈ Complex.re ⁻¹' Set.Ioi (1 : ℝ) := by
    change (1 : ℝ) < (2 : ℂ).re
    norm_num
  obtain ⟨fA, hfA⟩ := exists_archimedeanHeckeTest χ
  obtain ⟨f, a, ha, hf⟩ := exists_globalHeckeTest χ fA
  refine ⟨f, ?_⟩
  have h1 := hf ⟨2, hs⟩
  have h2 := hfA ⟨2, hs⟩
  rw [h1, h2]
  exact mul_ne_zero ha (mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (by norm_num))
    (finiteHeckeL_ne_zero_of_one_lt_re χ ⟨2, hs⟩))

/-- Left invariance of the idelic Haar measure turns a translate of the test function into the
value of the quasi-character at the translating idele. -/
private theorem archNuclearityDenominator_ne_bot_zeta_translate
    (u : IdeleGroup (𝓞 F) F) (f : ℬ(𝔸[F])) (c : HeckeCharacter (𝓞 F) F) :
    globalIdelicZetaIntegral (schwartzBruhatUnitTranslate u f) c =
      c (QuotientGroup.mk u) * globalIdelicZetaIntegral f c := by
  let : MeasurableSpace (IdeleGroup (𝓞 F) F) := borel _
  let : BorelSpace (IdeleGroup (𝓞 F) F) := ⟨rfl⟩
  let : (multiplicativeTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.1
  let d (g : IdeleGroup (𝓞 F) F) : ℂ := c (QuotientGroup.mk g)
  have hd (g k : IdeleGroup (𝓞 F) F) : d (g * k) = d g * d k := by
    change c (QuotientGroup.mk (g * k)) = _
    rw [QuotientGroup.mk_mul, map_mul]
  let b (g : IdeleGroup (𝓞 F) F) : ℂ := f (Multiplicative.ofAdd g.val) * d g
  change (∫ g : IdeleGroup (𝓞 F) F,
    f (Multiplicative.ofAdd ((↑u⁻¹ : 𝔸[F]) * g.val)) * d g
      ∂multiplicativeTamagawaMeasure F) = d u * ∫ g, b g ∂multiplicativeTamagawaMeasure F
  have he (g : IdeleGroup (𝓞 F) F) : d u * d (u⁻¹ * g) = d g :=
    (hd u (u⁻¹ * g)).symm.trans (congrArg d (mul_inv_cancel_left u g))
  have e (g : IdeleGroup (𝓞 F) F) :
      f (Multiplicative.ofAdd ((↑u⁻¹ : 𝔸[F]) * g.val)) * d g = d u * b (u⁻¹ * g) :=
    (congrArg (f (Multiplicative.ofAdd (u⁻¹ * g).val) * ·) (he g).symm).trans
      (mul_left_comm _ _ _)
  exact (integral_congr_ae (ae_of_all _ e)).trans
    ((integral_const_mul (d u) _).trans
      (congrArg (d u * ·) (integral_mul_left_eq_self b (u⁻¹))))

/-- A test whose homogeneous theta function vanishes has zero zeta integral on the half-plane
of absolute convergence, because the zeta integral is the Mellin integral of the theta function. -/
private theorem archNuclearityDenominator_ne_bot_zeta_of_theta
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (f : ℬ(𝔸[F]))
    (h : homogeneousAdelicThetaLinearMap F (ω(χ)) f = 0) (s : ℂ) (hs : 1 < s.re) :
    globalIdelicZetaIntegral f (ideleClassNormTwist χ s) = 0 := by
  let τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F :=
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleNorm F) := canonicalIdeleNormSection_rightInverse F
  have h1 := ((homogeneousThetaMellinIntegral_meromorphicContinuation τ (ω(χ)) f hτ χ
    (fun _ ↦ rfl) _).mpr rfl).2 (show s ∈ Complex.re ⁻¹' Ioi 1 from hs)
  refine ((globalIdelicZFunction_eq_integral f
    (archNuclearityDenominator_ne_bot_rightHalf χ s hs)).symm.trans h1).trans ?_
  refine (integral_congr_ae (ae_of_all _ fun t ↦ ?_)).trans (integral_zero _ _)
  have ht : homogeneousAdelicTheta (ω(χ)) f (QuotientGroup.mk (τ t)) = 0 :=
    DFunLike.congr_fun h (QuotientGroup.mk (τ t))
  exact mul_eq_zero_of_left ht _

/-- On the half-plane of absolute convergence the zeta integral is linear in the test. -/
private theorem archNuclearityDenominator_ne_bot_zeta_linear
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    ∃ L : ℬ(𝔸[F]) →ₗ[ℂ] ℂ,
      ∀ f, L f = globalIdelicZetaIntegral f (ideleClassNormTwist χ 2) := by
  let : MeasurableSpace (IdeleGroup (𝓞 F) F) := borel _
  have hc := archNuclearityDenominator_ne_bot_rightHalf χ 2 (by norm_num)
  have hint (f : ℬ(𝔸[F])) :=
    globalIdelicZetaIntegral_integrable f (ideleClassNormTwist χ 2) hc
  refine ⟨{ toFun := fun f ↦ globalIdelicZetaIntegral f (ideleClassNormTwist χ 2)
            map_add' := fun f g ↦ ?_
            map_smul' := fun r f ↦ ?_ }, fun f ↦ rfl⟩
  · refine Eq.trans ?_ (integral_add (hint f) (hint g))
    exact integral_congr_ae (ae_of_all _ fun x ↦ add_mul _ _ _)
  · refine Eq.trans ?_ (integral_const_mul r _)
    exact integral_congr_ae (ae_of_all _ fun x ↦ mul_assoc _ _ _)

/-- Some pure adelic tensor has a nonzero zeta integral at the square of the norm twist. -/
private theorem archNuclearityDenominator_ne_bot_pure
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    ∃ (a : ℬ(InfiniteAdeleRing F)) (b : ℬ(FiniteAdeleRing (𝓞 F) F)),
      globalIdelicZetaIntegral ((adeleSchwartz_inductiveTensor_equiv F).choose (a ⊗ₜ[ℂ] b))
        (ideleClassNormTwist χ 2) ≠ 0 := by
  obtain ⟨L, hL⟩ := archNuclearityDenominator_ne_bot_zeta_linear χ
  obtain ⟨f, hf⟩ := archNuclearityDenominator_ne_bot_zeta_ne_zero χ
  by_contra! h
  have hz : L.comp ((adeleSchwartz_inductiveTensor_equiv F).choose).toLinearMap = 0 :=
    TensorProduct.ext' fun a b ↦ (hL _).trans (h a b)
  have ht := LinearMap.congr_fun hz (((adeleSchwartz_inductiveTensor_equiv F).choose).symm f)
  change L ((adeleSchwartz_inductiveTensor_equiv F).choose
    (((adeleSchwartz_inductiveTensor_equiv F).choose).symm f)) = 0 at ht
  rw [((adeleSchwartz_inductiveTensor_equiv F).choose).apply_symm_apply, hL] at ht
  exact hf ht

/-- Cutting the archimedean factor off near the coordinate walls keeps the zeta integral of
some pure tensor nonzero, so a tensor with flat archimedean factor has that property. -/
private theorem archNuclearityDenominator_ne_bot_flat
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    ∃ (a : ℬ(InfiniteAdeleRing F)) (b : ℬ(FiniteAdeleRing (𝓞 F) F)),
      a ∈ archNuclearity_flatFactors (F := F) ∧
      globalIdelicZetaIntegral ((adeleSchwartz_inductiveTensor_equiv F).choose (a ⊗ₜ[ℂ] b))
        (ideleClassNormTwist χ 2) ≠ 0 := by
  obtain ⟨a₀, b₀, hab⟩ := archNuclearityDenominator_ne_bot_pure χ
  obtain ⟨J, hJ⟩ := archimedeanSchwartzBruhat_equiv (F := F)
  obtain ⟨k, hks, hkc, hkd, hk01, hklim⟩ :=
    archNuclearityDenominator_ne_bot_cutoff RealPlaces ComplexPlaces
  by_contra! h
  let h₀ : SchwartzMap Coordinates ℂ := J.symm a₀
  let φ (n : ℕ) : SchwartzMap Coordinates ℂ :=
    (show HasCompactSupport (fun x : Coordinates ↦ ((k n x : ℝ) : ℂ) * h₀ x) from
      ((hkc n).comp_left Complex.ofReal_zero).mul_right).toSchwartzMap
        ((Complex.ofRealCLM.contDiff.comp (hks n)).mul (h₀.smooth ⊤))
  have hflat (n : ℕ) :
      φ n ∈ archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces) :=
    mem_archimedeanFlatSchwartz_of_tsupport (φ n) ((hkd n).mono_left
      ((tsupport_mul_subset_left).trans (tsupport_comp_subset Complex.ofReal_zero _)))
  have hmem (n : ℕ) : J (φ n) ∈ archNuclearity_flatFactors (F := F) :=
    ⟨⟨φ n, hflat n⟩, fun x ↦ hJ (φ n) x⟩
  have hwall (g : IdeleGroup (𝓞 F) F) :
      ¬((∃ i, (InfiniteAdeleRing.ringEquiv_mixedSpace F g.val.1).1 i = 0) ∨
        ∃ j, (InfiniteAdeleRing.ringEquiv_mixedSpace F g.val.1).2 j = 0) := by
    have hxy : InfiniteAdeleRing.ringEquiv_mixedSpace F g.val.1 *
        InfiniteAdeleRing.ringEquiv_mixedSpace F g.inv.1 = 1 := by
      rw [← map_mul]
      exact (congrArg _ (congrArg Prod.fst g.val_inv)).trans (map_one _)
    rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · have h1 : (InfiniteAdeleRing.ringEquiv_mixedSpace F g.val.1).1 i *
          (InfiniteAdeleRing.ringEquiv_mixedSpace F g.inv.1).1 i = 1 :=
        congrArg (fun z : Coordinates ↦ z.1 i) hxy
      rw [hi, zero_mul] at h1
      exact zero_ne_one h1
    · have h1 : (InfiniteAdeleRing.ringEquiv_mixedSpace F g.val.1).2 j *
          (InfiniteAdeleRing.ringEquiv_mixedSpace F g.inv.1).2 j = 1 :=
        congrArg (fun z : Coordinates ↦ z.2 j) hxy
      rw [hj, zero_mul] at h1
      exact zero_ne_one h1
  let : MeasurableSpace (IdeleGroup (𝓞 F) F) := borel _
  have hc := archNuclearityDenominator_ne_bot_rightHalf χ 2 (by norm_num)
  let G (g : IdeleGroup (𝓞 F) F) : ℂ :=
    (adeleSchwartz_inductiveTensor_equiv F).choose (a₀ ⊗ₜ[ℂ] b₀)
      (Multiplicative.ofAdd g.val) * ideleClassNormTwist χ 2 (QuotientGroup.mk g)
  let K (n : ℕ) (g : IdeleGroup (𝓞 F) F) : ℝ :=
    k n (InfiniteAdeleRing.ringEquiv_mixedSpace F g.val.1)
  have hpt (n : ℕ) (g : IdeleGroup (𝓞 F) F) :
      (adeleSchwartz_inductiveTensor_equiv F).choose (J (φ n) ⊗ₜ[ℂ] b₀)
          (Multiplicative.ofAdd g.val) * ideleClassNormTwist χ 2 (QuotientGroup.mk g) =
        (K n g : ℂ) * G g := by
    have ha₀ : a₀ (Multiplicative.ofAdd g.val.1) =
        h₀ (InfiniteAdeleRing.ringEquiv_mixedSpace F g.val.1) := by
      rw [← hJ, J.apply_symm_apply]
    change _ = (K n g : ℂ) * ((adeleSchwartz_inductiveTensor_equiv F).choose
      (a₀ ⊗ₜ[ℂ] b₀) (Multiplicative.ofAdd g.val) *
        ideleClassNormTwist χ 2 (QuotientGroup.mk g))
    rw [(adeleSchwartz_inductiveTensor_equiv F).choose_spec,
      (adeleSchwartz_inductiveTensor_equiv F).choose_spec, hJ, ha₀]
    change ((k n _ : ℝ) : ℂ) * h₀ _ * _ * _ = (K n g : ℂ) * (_ * _ * _)
    simp only [K, mul_assoc]
  have hzero := archNuclearityDenominator_ne_bot_limit (multiplicativeTamagawaMeasure F) G
    (globalIdelicZetaIntegral_integrable _ (ideleClassNormTwist χ 2) hc) K
    (fun n g ↦ hk01 n _) (fun g ↦ hklim _ (hwall g))
    (fun n ↦ (globalIdelicZetaIntegral_integrable ((adeleSchwartz_inductiveTensor_equiv F).choose
      (J (φ n) ⊗ₜ[ℂ] b₀)) (ideleClassNormTwist χ 2) hc).congr (ae_of_all _ (hpt n)))
    (fun n ↦ (integral_congr_ae (ae_of_all _ (hpt n))).symm.trans (h (J (φ n)) b₀ (hmem n)))
  exact hab hzero

/-- A polar test with flat archimedean factors whose homogeneous theta class is not zero:
a flat pure tensor with nonzero zeta integral, corrected by a translate under an
archimedean idele of norm two so that its Fourier value at the origin vanishes. -/
private theorem archNuclearityDenominator_ne_bot_witness
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    ∃ f : P, f.val ∈ globalArchimedeanFlatTests F ∧ mkΘ(χ, f) ≠ 0 := by
  obtain ⟨a, b, ha, hZ⟩ := archNuclearityDenominator_ne_bot_flat χ
  obtain ⟨L, hL⟩ := archNuclearityDenominator_ne_bot_zeta_linear χ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let t : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
  let g := singlePlaceIdeleNormSection F w t
  let u := Units.map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom g
  have hu : archNuclearity_archUnit u = g := Units.ext (Prod.ext rfl rfl)
  have hnorm : ideleNorm F (archNuclearity_archUnit u) = t :=
    hu ▸ singlePlaceIdeleNormSection_rightInverse F w t
  have hval : ((((ideleNorm F (archNuclearity_archUnit u)).val : ℝ)) : ℂ) = 2 := by
    rw [hnorm]
    change (((2 : ℝ≥0) : ℝ) : ℂ) = 2
    norm_num
  let f₀ := (adeleSchwartz_inductiveTensor_equiv F).choose (a ⊗ₜ[ℂ] b)
  let a' := schwartzBruhatUnitTranslate u a - (2 : ℂ) • a
  have ha' : a' ∈ archNuclearity_flatFactors (F := F) :=
    Submodule.sub_mem _ (archNuclearity_flatFactors_translate u a ha) (Submodule.smul_mem _ _ ha)
  let f₁ := (adeleSchwartz_inductiveTensor_equiv F).choose (a' ⊗ₜ[ℂ] b)
  have htA := archNuclearity_translate_pure u (1 : (FiniteAdeleRing (𝓞 F) F)ˣ) a b
  rw [archNuclearity_translate_one,
    show archNuclearity_finiteUnit (F := F) 1 = 1 from Units.ext rfl, mul_one] at htA
  have hf₁ :
      f₁ = schwartzBruhatUnitTranslate (archNuclearity_archUnit u) f₀ - (2 : ℂ) • f₀ := by
    have h1 : a' ⊗ₜ[ℂ] b =
        schwartzBruhatUnitTranslate u a ⊗ₜ[ℂ] b - (2 : ℂ) • (a ⊗ₜ[ℂ] b) :=
      (TensorProduct.sub_tmul _ _ _).trans
        (congrArg (schwartzBruhatUnitTranslate u a ⊗ₜ[ℂ] b - ·)
          (TensorProduct.smul_tmul' _ _ _).symm)
    exact (congrArg (adeleSchwartz_inductiveTensor_equiv F).choose h1).trans
      ((map_sub (adeleSchwartz_inductiveTensor_equiv F).choose _ _).trans
        (congrArg₂ (· - ·) htA.symm
          (map_smul (adeleSchwartz_inductiveTensor_equiv F).choose _ _)))
  have hflat : f₁ ∈ globalArchimedeanFlatTests F := by
    obtain ⟨h, hh⟩ := ha'
    exact Submodule.subset_span ⟨a', b, h, hh, fun hF ↦ hF.elim, rfl⟩
  let H : ℬ(𝔸[F]) →L[ℂ] ℂ := (ContinuousLinearMap.snd ℂ ℂ ℂ).comp
    (⟨(adelePolarValues_isLinear (F := F)).mk' adelePolarValues,
      adelePolarValues_continuous⟩ : ℬ(𝔸[F]) →L[ℂ] ℂ × ℂ)
  have hH : H f₁ = 0 := by
    have h := archNuclearity_hatC_translate (archNuclearity_archUnit u) f₀
    rw [hval] at h
    rw [hf₁, map_sub, map_smul, smul_eq_mul]
    exact sub_eq_zero.mpr h
  have hP : f₁ ∈ P := (globalArchimedeanFlatTests_zero_moments f₁ hflat).2.mpr hH
  refine ⟨⟨f₁, hP⟩, hflat, fun h0 ↦ ?_⟩
  have hker : (⟨f₁, hP⟩ : P) ∈ Π(χ) := (Submodule.Quotient.mk_eq_zero _).mp h0
  have hθ : homogeneousAdelicThetaLinearMap F (ω(χ)) f₁ = 0 := LinearMap.mem_ker.mp hker
  have hZ1 := archNuclearityDenominator_ne_bot_zeta_of_theta χ f₁ hθ 2 (by norm_num)
  have hZt := archNuclearityDenominator_ne_bot_zeta_translate (archNuclearity_archUnit u) f₀
    (ideleClassNormTwist χ 2)
  have hlin : L f₁ =
      L (schwartzBruhatUnitTranslate (archNuclearity_archUnit u) f₀) - 2 * L f₀ := by
    rw [hf₁, map_sub, map_smul, smul_eq_mul]
  rw [hL, hL, hL, hZ1, hZt, ← sub_mul] at hlin
  have hcU : ideleClassNormTwist χ 2 (QuotientGroup.mk (archNuclearity_archUnit u)) - 2 ≠ 0 := by
    intro h2
    have h3 : ((χ (QuotientGroup.mk (archNuclearity_archUnit u)) : Circle) : ℂ) *
        (((ideleNorm F (archNuclearity_archUnit u)).val : ℝ) : ℂ) ^ (2 : ℂ) = 2 :=
      sub_eq_zero.mp h2
    rw [hval] at h3
    have h4 := congrArg norm h3
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.cpow_ofNat, norm_pow, Complex.norm_ofNat] at h4
    norm_num at h4
  exact hZ ((mul_eq_zero.mp hlin.symm).resolve_left hcU)

/-- Paper: Theorem 7.4.3.1(1), p. 368.
The archimedean-flat theta image is nontrivial: some archimedean-flat test whose
archimedean factors have zero additive integral has a nonzero class in the
zero-moment theta space.

A proof needs an explicit witness, and two routes are open. Either produce a nonzero
flat archimedean factor of zero additive integral together with a finite test that
the theta map does not kill; the comment above this section records that a
difference of dilates of a bump times the characteristic function of the integer
units has that shape on the trivial norm-one component. Or use
`archNuclearityMellin_range`, which is stated below this point: the Mellin image
of the denominator is the Schwartz-Bergman part of the ideal generated by
`archRegularizedFiniteHeckeL χ τ hτ`, so the denominator is trivial only if that
generator has no nonzero Schwartz-Bergman multiple; on `1 < Re s` its value is a
product of two nonzero factors by `archRegularizedFiniteHeckeL_apply` and
`finiteHeckeL_ne_zero_of_one_lt_re`. -/
private theorem archNuclearityDenominator_ne_bot :
    archNuclearityDenominator χ ≠ ⊥ := by
  obtain ⟨f, hf, hne⟩ := archNuclearityDenominator_ne_bot_witness χ
  exact (Submodule.ne_bot_iff _).mpr ⟨mkΘ(χ, f),
    (mem_archNuclearityDenominator_iff_flatPolarImage χ _).mpr ⟨f, hf, rfl⟩, hne⟩

/-- Paper: Theorem 7.4.3.1(1), p. 368.
The zero-moment archimedean-flat theta image is nonzero and closed.
Deviation: Uses the Fourier-moment correction from the prose after (7.4.3.1).
Without it the printed image need not be contained in the zero-moment theta space. -/
theorem archNuclearityDenominator_nonzero_closed :
    archNuclearityDenominator χ ≠ ⊥ ∧
      IsClosed (archNuclearityDenominator χ : Set (Θ₀(χ))) :=
  ⟨archNuclearityDenominator_ne_bot χ,
    archNuclearityDenominator_isClosed_jetEquiv (χ := χ)
      ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
      (canonicalIdeleNormSection_rightInverse F)⟩

/-- Paper: Theorem 7.4.3.1(5), pp. 368–369.
The strong dual of the archimedean quotient carries the finest locally convex topology. -/
theorem archNuclearityStrongDual_finest :
    let E := StrongDual ℂ (ArchNuclearityQuotient χ)
    (inferInstance : TopologicalSpace E) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex E)) := by
  obtain ⟨q⟩ := archNuclearityStrongDual_finest_sequenceEquiv χ
  obtain ⟨t, _⟩ := realSchwartzTaylor_equiv
  obtain ⟨p, _⟩ := realDiracDerivatives_polynomialEquiv
  let : TopologicalSpace (PowerSeries ℂ) := inferInstanceAs (TopologicalSpace ((Unit →₀ ℕ) → ℂ))
  let idx := (Finsupp.uniqueLinearEquiv ℕ ℕ ()).symm.toEquiv
  let series := ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Unit →₀ ℕ ↦ ℂ) idx
  let e := (q.trans series).trans t.symm
  exact archNuclearityStrongDual_finest_of_equiv
    (p.trans (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ)))

local notation "Aθ(" φ ")" => (exists_polarThetaNuclearityAction χ τ hτ φ).choose

/-- Paper: Theorem 7.4.3.2(1), p. 372.
The archimedean-flat theta denominator is a closed subspace stable under the
regularized action of every Bruhat test. -/
theorem archNuclearityDenominator_closed_invariant (φ : 𝒟) :
    let D := archNuclearityDenominator χ
    IsClosed (D : Set (Θ₀(χ))) ∧ Set.MapsTo (Aθ(φ)) (D : Set (Θ₀(χ))) D := by
  let D := archNuclearityDenominator χ
  obtain ⟨e, he⟩ := archNuclearityQuotient_jetEquiv χ τ hτ
  have hmem (x : Θ₀(χ)) : x ∈ D ↔ ∀ j, archNuclearityJet χ τ hτ j x = 0 := by
    rw [← Submodule.Quotient.mk_eq_zero D]
    change (archNuclearityDenominator χ).mkQ x = (0 : ArchNuclearityQuotient χ) ↔ _
    constructor
    · intro hx j
      rw [← he x j, hx, map_zero, Pi.zero_apply]
    · intro hx
      apply e.injective
      funext j
      rw [he x j, hx j, map_zero, Pi.zero_apply]
  have hjet (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ) :
      archNuclearityJet χ τ hτ j x = iteratedDeriv j.val.2 ((Z(χ, τ, hτ)) x).val j.val.1 := by
    unfold archNuclearityJet
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
    exact congrArg (fun g : ℂ → ℂ ↦ iteratedDeriv j.val.2 g j.val.1)
      (funext (schwartzBergmanEntireInclusion_apply _))
  constructor
  · rw [show (D : Set (Θ₀(χ))) = ⋂ j, (archNuclearityJet χ τ hτ j) ⁻¹' {0} by
      apply Set.ext
      intro x
      rw [mem_iInter]
      exact hmem x]
    exact isClosed_iInter fun j ↦ isClosed_singleton.preimage (archNuclearityJet χ τ hτ j).continuous
  · intro x hx
    apply (hmem _).mpr
    intro j
    let v := (Z(χ, τ, hτ)) x
    have hv : Differentiable ℂ v.val := fun z ↦
      (v.property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    have hprod : ((Z(χ, τ, hτ)) (Aθ(φ) x)).val = nuclearityTestMellin χ φ * v.val :=
      funext ((exists_polarThetaNuclearityAction χ τ hτ φ).choose_spec.1 x)
    rw [hjet, hprod, iteratedDeriv_mul
      ((archNuclearityDenominator_closed_invariant_multiplier χ φ).contDiff.contDiffAt)
      hv.contDiff.contDiffAt]
    apply Finset.sum_eq_zero
    intro i _
    have hk := (hmem x).mp hx ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩
    rw [hjet] at hk
    exact mul_eq_zero_of_right _ hk

/-- A test supported where the modulus lies in `[r, R]` has Mellin transform bounded by
`(r^σ + R^σ) ∫ ‖φ‖` on the line of real part `σ`. -/
private theorem archNuclearity_trace_mellin_bound {G : Type*} [MeasurableSpace G]
    (μ : Measure G) (φ : G → ℂ) (hφ : Integrable (fun g ↦ ‖φ g‖) μ) (n : G → ℝ) (r R : ℝ)
    (hr : 0 < r) (hsupp : ∀ g, φ g ≠ 0 → r ≤ n g ∧ n g ≤ R) (w : G → ℂ) (σ : ℝ)
    (hw : ∀ g, φ g ≠ 0 → ‖w g‖ = n g ^ σ) :
    ‖∫ g, φ g * w g ∂μ‖ ≤ (r ^ σ + R ^ σ) * ∫ g, ‖φ g‖ ∂μ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hφ.const_mul _) (ae_of_all _ fun g ↦ ?_)
  by_cases h0 : φ g = 0
  · simp only [h0, zero_mul, norm_zero, mul_zero, le_refl]
  obtain ⟨hlo, hhi⟩ := hsupp g h0
  have hn : 0 < n g := hr.trans_le hlo
  rw [norm_mul, hw g h0, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rcases le_total 0 σ with hσ | hσ
  · exact (Real.rpow_le_rpow hn.le hhi hσ).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hr.le σ))
  · exact (Real.rpow_le_rpow_of_nonpos hr hlo hσ).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (hn.trans_le hhi).le σ))

/-- Poles at `-c v - k` with bounded orders, and transforms bounded by `r^σ + R^σ` with
`1 < r ≤ R`, give an absolutely convergent pole sum. -/
private theorem archNuclearity_trace_pole_summable {W : Type*} [Finite W] (c : W → ℂ)
    (ord : ℂ → ℕ) (N : ℕ) (hord : ∀ z, ord z ≤ N)
    (hpole : ∀ z, 0 < ord z → ∃ v, ∃ k : ℕ, z = -c v - k) (M : ℂ → ℂ) (K r R : ℝ)
    (hK : 0 ≤ K) (hr : 1 < r) (hR : 1 < R)
    (hM : ∀ z, ‖M z‖ ≤ (r ^ z.re + R ^ z.re) * K) :
    Summable fun z : ℂ ↦ (ord z : ℝ) * ‖M z‖ := by
  classical
  let Pz := {z : ℂ // 0 < ord z}
  have hsub : ∀ x ∉ Set.range (Subtype.val : Pz → ℂ), (ord x : ℝ) * ‖M x‖ = 0 := by
    intro x hx
    have : ord x = 0 := by
      by_contra h
      exact hx ⟨⟨x, Nat.pos_of_ne_zero h⟩, rfl⟩
    simp [this]
  rw [← Function.Injective.summable_iff Subtype.val_injective hsub]
  choose v k hvk using fun z : Pz ↦ hpole z.val z.property
  let ι : Pz → W × ℕ := fun z ↦ (v z, k z)
  have hι : Function.Injective ι := by
    intro a b h
    apply Subtype.ext
    rw [hvk a, hvk b]
    simp only [ι, Prod.mk.injEq] at h
    rw [h.1, h.2]
  let g : W × ℕ → ℝ := fun p ↦ N * K * (r ^ (-(c p.1).re) * (r⁻¹) ^ p.2 +
    R ^ (-(c p.1).re) * (R⁻¹) ^ p.2)
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hNK : 0 ≤ (N : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK
  have hg0 (p : W × ℕ) : 0 ≤ g p :=
    mul_nonneg hNK (add_nonneg
      (mul_nonneg (Real.rpow_nonneg hr0.le _) (pow_nonneg (inv_nonneg.mpr hr0.le) _))
      (mul_nonneg (Real.rpow_nonneg hR0.le _) (pow_nonneg (inv_nonneg.mpr hR0.le) _)))
  have hg : Summable g := by
    refine (summable_prod_of_nonneg hg0).mpr ⟨fun x ↦ ?_, Summable.of_finite⟩
    have h1 : Summable fun y : ℕ ↦ r ^ (-(c x).re) * (r⁻¹) ^ y :=
      Summable.mul_left (r ^ (-(c x).re))
        (summable_geometric_of_lt_one (inv_nonneg.mpr hr0.le) (inv_lt_one_of_one_lt₀ hr))
    have h2 : Summable fun y : ℕ ↦ R ^ (-(c x).re) * (R⁻¹) ^ y :=
      Summable.mul_left (R ^ (-(c x).re))
        (summable_geometric_of_lt_one (inv_nonneg.mpr hR0.le) (inv_lt_one_of_one_lt₀ hR))
    have h3 := Summable.mul_left ((N : ℝ) * K) (h1.add h2)
    exact h3
  refine Summable.of_nonneg_of_le (fun _ ↦ mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    (fun z ↦ ?_) (hg.comp_injective hι)
  have hz : (z.val).re = -(c (v z)).re - k z := by
    rw [hvk z]
    simp
  have hpow (a : ℝ) (ha : 0 < a) : a ^ (z.val).re = a ^ (-(c (v z)).re) * (a⁻¹) ^ k z := by
    rw [hz, Real.rpow_sub ha, Real.rpow_natCast, div_eq_mul_inv, inv_pow]
  change (ord z.val : ℝ) * ‖M z.val‖ ≤ N * K * (r ^ (-(c (v z)).re) * (r⁻¹) ^ k z +
    R ^ (-(c (v z)).re) * (R⁻¹) ^ k z)
  rw [← hpow r hr0, ← hpow R hR0, mul_assoc, mul_comm K]
  exact mul_le_mul (by exact_mod_cast hord _) (hM _) (norm_nonneg _) (Nat.cast_nonneg _)

/-- Summing a function of the center over all jet indices counts each center with its
multiplicity, in any enumeration of the indices. -/
private theorem archNuclearity_trace_reindex (m : ℂ → ℕ) (M : ℂ → ℂ)
    (σ : ℕ ≃ {j : ℂ × ℕ // j.2 < m j.1})
    (h : Summable fun z : ℂ ↦ (m z : ℝ) * ‖M z‖) :
    Summable (fun n ↦ ‖M (σ n).val.1‖) ∧
      HasSum (fun n ↦ M (σ n).val.1) (∑' z, (m z : ℂ) * M z) := by
  let J := {j : ℂ × ℕ // j.2 < m j.1}
  let e : J ≃ Σ z : ℂ, Fin (m z) :=
    { toFun := fun j ↦ ⟨j.val.1, ⟨j.val.2, j.property⟩⟩
      invFun := fun p ↦ ⟨(p.1, p.2.val), p.2.isLt⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let f : (Σ z : ℂ, Fin (m z)) → ℂ := fun p ↦ M p.1
  have hfib (z : ℂ) : ∑' _ : Fin (m z), ‖M z‖ = (m z : ℝ) * ‖M z‖ := by
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnorm : Summable fun p ↦ ‖f p‖ :=
    (summable_sigma_of_nonneg fun _ ↦ norm_nonneg _).mpr
      ⟨fun _ ↦ Summable.of_finite, by simpa only [f, hfib] using h⟩
  have hf : Summable f := hnorm.of_norm
  have hsum : ∑' p, f p = ∑' z, (m z : ℂ) * M z := by
    rw [hf.tsum_sigma' fun _ ↦ Summable.of_finite]
    refine tsum_congr fun z ↦ ?_
    rw [tsum_fintype]
    change ∑ _b : Fin (m z), M z = _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcomp : (fun n ↦ M (σ n).val.1) = f ∘ (σ.trans e) := rfl
  have hcompn : (fun n ↦ ‖M (σ n).val.1‖) = (fun p ↦ ‖f p‖) ∘ (σ.trans e) := rfl
  refine ⟨?_, ?_⟩
  · rw [hcompn]
    exact (σ.trans e).summable_iff.mpr hnorm
  · rw [hcomp, ← hsum]
    exact (σ.trans e).hasSum_iff.mpr hf.hasSum

/-- A biorthogonal coefficient functional picks out the coefficient of its own vector
from a finite combination in which that vector occurs exactly once. -/
private theorem archNuclearity_trace_diag {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    (d : ℕ → E) (b : ℕ → E →ₗ[ℂ] ℂ) (hb : ∀ m n, b m (d n) = if m = n then 1 else 0)
    (n : ℕ) (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ s) (coef : ι → ℂ) (idx : ι → ℕ)
    (h₀ : idx i₀ = n) (hne : ∀ i ∈ s, i ≠ i₀ → idx i ≠ n) :
    b n (∑ i ∈ s, coef i • d (idx i)) = coef i₀ := by
  rw [map_sum, Finset.sum_eq_single i₀]
  · simp [hb, h₀]
  · intro i hi hi'
    have hn : ¬ n = idx i := fun h ↦ hne i hi hi' h.symm
    simp [hb, hn]
  · intro h
    exact absurd hi₀ h

/-- A Bruhat test supported where the norm exceeds one has Mellin transform bounded by
`(r^σ + R^σ) K` on the line of real part `σ`, for some `1 < r` and `1 < R`: the norm is
bounded above and below on the compact support. -/
private theorem archNuclearity_trace_mellin (φ : 𝒟)
    (hφ : tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)}) :
    ∃ K r R : ℝ, 0 ≤ K ∧ 1 < r ∧ 1 < R ∧
      ∀ z, ‖nuclearityTestMellin χ φ z‖ ≤ (r ^ z.re + R ^ z.re) * K := by
  let n : C𝔽 → ℝ := fun g ↦ ((ideleClassNorm F g).val : ℝ)
  have hn : Continuous n := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hK : IsCompact (tsupport φ.val) := φ.property.2
  obtain ⟨r, R, hr, hR, hrR⟩ : ∃ r R : ℝ, 1 < r ∧ 1 < R ∧
      ∀ g ∈ tsupport φ.val, r ≤ n g ∧ n g ≤ R := by
    rcases (tsupport φ.val).eq_empty_or_nonempty with he | hne
    · exact ⟨2, 2, by norm_num, by norm_num, fun g hg ↦ by simp [he] at hg⟩
    · obtain ⟨a, ha, hamin⟩ := hK.exists_isMinOn hne hn.continuousOn
      obtain ⟨b, hb, hbmax⟩ := hK.exists_isMaxOn hne hn.continuousOn
      exact ⟨n a, n b, hφ ha, hφ hb, fun g hg ↦
        ⟨isMinOn_iff.mp hamin g hg, isMaxOn_iff.mp hbmax g hg⟩⟩
  have htw (s : ℂ) (g : C𝔽) : ‖ideleClassNormTwist χ s g‖ = n g ^ s.re := by
    change ‖(χ g : ℂ) * ((n g : ℝ) : ℂ) ^ s‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
  have hint : Integrable (fun g ↦ ‖φ.val g‖) μ𝔽 := by
    refine ((nuclearityTestMellin_integrable χ φ).1 0).norm.congr (ae_of_all _ fun g ↦ ?_)
    change ‖φ.val g * ideleClassNormTwist χ 0 g‖ = ‖φ.val g‖
    rw [norm_mul, htw, Complex.zero_re, Real.rpow_zero, mul_one]
  refine ⟨∫ g, ‖φ.val g‖ ∂μ𝔽, r, R, integral_nonneg fun _ ↦ norm_nonneg _, hr, hR,
    fun z ↦ ?_⟩
  exact archNuclearity_trace_mellin_bound μ𝔽 φ.val hint n r R (zero_lt_one.trans hr)
    (fun g hg ↦ hrR g (subset_tsupport _ hg)) (ideleClassNormTwist χ z) z.re
    (fun g _ ↦ htw z g)

/-- On a trivial norm-one isotype the omitted jet sits at a gamma pole, and the
norm twist of `χ` there is the trivial quasi-character. -/
private theorem archNuclearity_trace_trivial (hω : ω(χ) = 1) :
    1 ≤ gammaOrder(χ, atZeroPole(χ, τ, hτ)) ∧
      ∀ g, ideleClassNormTwist χ atZeroPole(χ, τ, hτ) g = ideleClassNormTwist 1 0 g := by
  have hk : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext1 u
    exact DFunLike.congr_fun hω u
  obtain ⟨hZ, heZ⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨t, ⟨hc, -, -, -⟩, -⟩ := completedHeckeL_continuation_simplePoles χ _ hZ heZ hk
  let b : ℂ := Complex.I * (t : ℂ)
  have hphase := existsUnique_ideleNormSection_character_phase χ τ hτ
  have hx : -t = hphase.exists.choose := by
    apply hphase.unique _ hphase.exists.choose_spec
    intro u
    have he := DFunLike.congr_fun hc (QuotientGroup.mk (τ u))
    change (χ (QuotientGroup.mk (τ u)) : ℂ) * _ ^ (0 : ℂ) =
      1 * ((((ideleNorm F (τ u)).val : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ))) at he
    rw [Complex.cpow_zero, mul_one, one_mul, hτ u] at he
    simpa only [Complex.ofReal_neg, neg_mul, mul_comm (t : ℂ) Complex.I] using he
  have hpole : atZeroPole(χ, τ, hτ) = b := by
    change -(hphase.exists.choose : ℂ) * Complex.I = b
    rw [← hx, Complex.ofReal_neg, neg_neg, mul_comm]
  rw [hpole]
  have hR0 : (heckeGammaFactor χ b)⁻¹ = 0 := by
    have hshift := heckeGammaFactor_of_normTwist χ (-Complex.I * (t : ℂ))
      (by simp [Complex.mul_re]) hc b
    have hneg : b + -Complex.I * (t : ℂ) = 0 := by
      dsimp [b]
      ring
    rw [hshift, hneg]
    simpa using inv_heckeGammaFactor_one_neg_even (F := F) 0
  have han : AnalyticOnNhd ℂ (fun s ↦ (heckeGammaFactor χ s)⁻¹) univ :=
    fun s _ ↦ (differentiable_inv_heckeGammaFactor χ).analyticAt s
  have hne0 : analyticOrderAt (fun s ↦ (heckeGammaFactor χ s)⁻¹) b ≠ 0 := by
    rw [Ne, (han b (mem_univ _)).analyticOrderAt_eq_zero, not_not]
    exact hR0
  have hnetop : analyticOrderAt (fun s ↦ (heckeGammaFactor χ s)⁻¹) b ≠ ⊤ := by
    intro htop
    have h1 : (heckeGammaFactor χ 1)⁻¹ ≠ 0 :=
      inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (by norm_num))
    exact h1 (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ b) (analyticOrderAt_eq_top.1 htop) (mem_univ 1))
  refine ⟨?_, fun g ↦ ?_⟩
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hnetop
    rw [← hm] at hne0 ⊢
    rw [ENat.toNat_natCast]
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne0)
  · have hx0 : ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    have he := DFunLike.congr_fun hc g
    change (χ g : ℂ) * ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) =
      1 * ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ)) at he
    change (χ g : ℂ) * ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ b =
      1 * ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ)
    rw [Complex.cpow_zero, mul_one, one_mul] at he
    rw [he, ← Complex.cpow_add _ _ hx0, show -Complex.I * (t : ℂ) + b = 0 by dsimp [b]; ring,
      Complex.cpow_zero, mul_one]

/-- Continuous functionals on a quotient agree once they agree on representatives. -/
private theorem archNuclearity_trace_qext {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (D : Submodule ℂ E) (f g : StrongDual ℂ (E ⧸ D))
    (h : ∀ x, f (D.mkQ x) = g (D.mkQ x)) : f = g :=
  ContinuousLinearMap.ext fun q ↦ by
    obtain ⟨x, rfl⟩ := D.mkQ_surjective q
    exact h x

/-- Abstract form of the diagonal computation: if an operator `A` acts on jet coordinates by
the Leibniz rule with multiplier derivatives `Md i`, then for biorthogonal coefficient
functionals the diagonal entry of the induced quotient operator is the multiplier at the
center of the jet. -/
private theorem archNuclearity_trace_diagonal {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (D : Submodule ℂ E) (A : E →ₗ[ℂ] E) (T : (E ⧸ D) →L[ℂ] (E ⧸ D))
    (hT : ∀ x, T (D.mkQ x) = D.mkQ (A x)) (m : ℂ → ℕ)
    (σ : ℕ ≃ {j : ℂ × ℕ // j.2 < m j.1}) (jet : {j : ℂ × ℕ // j.2 < m j.1} → E → ℂ)
    (Md : ℕ → ℂ → ℂ) (M₀ : ℂ → ℂ) (hMd₀ : ∀ z, Md 0 z = M₀ z)
    (hjetA : ∀ x (j : {j : ℂ × ℕ // j.2 < m j.1}), jet j (A x) =
      ∑ i ∈ Finset.range (j.val.2 + 1), (j.val.2.choose i : ℂ) * Md i j.val.1 *
        jet ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩ x)
    (d : ℕ → StrongDual ℂ (E ⧸ D)) (b : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ D)))
    (hd : ∀ n x, d n (D.mkQ x) = jet (σ n) x)
    (hb : ∀ m n, b m (d n) = if m = n then 1 else 0) (n : ℕ) :
    b n ((d n).comp T) = M₀ (σ n).val.1 := by
  have hcomp : (d n).comp T = ∑ i ∈ Finset.range ((σ n).val.2 + 1),
      (((σ n).val.2.choose i : ℂ) * Md i (σ n).val.1) •
        d (σ.symm ⟨((σ n).val.1, (σ n).val.2 - i),
          (Nat.sub_le _ _).trans_lt (σ n).property⟩) := by
    refine archNuclearity_trace_qext D _ _ fun x ↦ ?_
    rw [ContinuousLinearMap.comp_apply, hT, hd, hjetA, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ContinuousLinearMap.smul_apply, hd, Equiv.apply_symm_apply, smul_eq_mul]
  rw [hcomp]
  refine (archNuclearity_trace_diag d (fun m ↦ (b m).toLinearMap) hb n
    (Finset.range ((σ n).val.2 + 1)) 0 (by simp)
    (fun i ↦ ((σ n).val.2.choose i : ℂ) * Md i (σ n).val.1)
    (fun i ↦ σ.symm ⟨((σ n).val.1, (σ n).val.2 - i),
      (Nat.sub_le _ _).trans_lt (σ n).property⟩) ?_ ?_).trans ?_
  · rw [Equiv.symm_apply_eq]
    exact Subtype.ext (Prod.ext rfl (Nat.sub_zero _))
  · intro i hi hi0 heq
    rw [Equiv.symm_apply_eq] at heq
    have h2 := congrArg (fun j : {j : ℂ × ℕ // j.2 < m j.1} ↦ j.val.2) heq
    have hik := Finset.mem_range.mp hi
    simp only at h2
    omega
  · simp [hMd₀]

/-- The scalar half of Theorem 7.4.3.2(2): the gamma-pole series converges absolutely, and
for every enumeration of the jets the Mellin values at the jet centers sum absolutely to
the pole series minus the omitted trivial jet. -/
private theorem archNuclearity_trace_scalar (φ : 𝒟)
    (hφ : tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)}) :
    let poles := {z : ℂ // 0 < gammaOrder(χ, z)}
    let term := fun z : poles ↦ (gammaOrder(χ, z.val) : ℂ) * nuclearityTestMellin χ φ z.val
    let correction := if ω(χ) = 1 then nuclearityTestMellin 1 φ 0 else 0
    Summable (fun z ↦ ‖term z‖) ∧ ∀ σ : ℕ ≃ ArchNuclearityJetIndex χ τ hτ,
      Summable (fun n ↦ ‖nuclearityTestMellin χ φ (σ n).val.1‖) ∧
      HasSum (fun n ↦ nuclearityTestMellin χ φ (σ n).val.1) ((∑' z, term z) - correction) := by
  intro poles term correction
  classical
  let M := nuclearityTestMellin χ φ
  obtain ⟨c, hc⟩ := archNuclearity_trace_gammaOrder χ
  obtain ⟨K, r, R, hK, hr, hR, hM⟩ := archNuclearity_trace_mellin χ φ hφ
  have hsum : Summable fun z : ℂ ↦ (gammaOrder(χ, z) : ℝ) * ‖M z‖ :=
    archNuclearity_trace_pole_summable c (fun z ↦ gammaOrder(χ, z)) _ (fun z ↦ (hc z).1)
      (fun z ↦ (hc z).2) M K r R hK hr hR hM
  refine ⟨(hsum.subtype fun z ↦ 0 < gammaOrder(χ, z)).congr fun z ↦ ?_, fun σ ↦ ?_⟩
  · simp only [Function.comp_apply, term, norm_mul, Complex.norm_natCast]
    rfl
  let mult := archNuclearityMultiplicity χ τ hτ
  have hmult : Summable fun z : ℂ ↦ (mult z : ℝ) * ‖M z‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      (fun z ↦ mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (norm_nonneg _))
      hsum
  obtain ⟨h1, h2⟩ := archNuclearity_trace_reindex mult M σ hmult
  refine ⟨h1, ?_⟩
  convert h2 using 1
  have hsupp : Function.support (fun z : ℂ ↦ (gammaOrder(χ, z) : ℂ) * M z) ⊆
      {z | 0 < gammaOrder(χ, z)} := by
    intro z hz
    by_contra h
    simp only [Set.mem_ofPred_eq, not_lt, Nat.le_zero] at h
    exact hz (by simp [h])
  have htsum : ∑' z : poles, term z = ∑' z : ℂ, (gammaOrder(χ, z) : ℂ) * M z :=
    tsum_subtype_eq_of_support_subset (s := {z | 0 < gammaOrder(χ, z)}) hsupp
  have hsumC : Summable fun z : ℂ ↦ (gammaOrder(χ, z) : ℂ) * M z :=
    Summable.of_norm (by simpa only [norm_mul, Complex.norm_natCast] using hsum)
  rw [htsum]
  by_cases hω : ω(χ) = 1
  · obtain ⟨hord1, htw⟩ := archNuclearity_trace_trivial χ τ hτ hω
    have hm (z : ℂ) : (mult z : ℂ) * M z = (gammaOrder(χ, z) : ℂ) * M z -
        if z = atZeroPole(χ, τ, hτ) then M atZeroPole(χ, τ, hτ) else 0 := by
      simp only [mult, archNuclearityMultiplicity, hω, true_and]
      split_ifs with h
      · subst h
        rw [Nat.cast_sub hord1]
        ring
      · simp
    have hcorr : correction = M atZeroPole(χ, τ, hτ) := by
      simp only [correction, hω, ↓reduceIte]
      refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
      change φ.val g * ideleClassNormTwist 1 0 g = φ.val g * ideleClassNormTwist χ _ g
      rw [htw g]
    rw [tsum_congr hm, hsumC.tsum_sub (hasSum_ite_eq _ _).summable, tsum_ite_eq, hcorr]
  · have hm (z : ℂ) : (mult z : ℂ) * M z = (gammaOrder(χ, z) : ℂ) * M z := by
      simp [mult, archNuclearityMultiplicity, hω]
    simp only [correction, hω, ↓reduceIte, sub_zero]
    exact (tsum_congr hm).symm


-- TODO(paper-gap): The contour identity (7.4.3.15) uses positive pole orders
-- on the right, but the logarithmic derivative has their negatives as residues.
-- Both boundary lines must avoid the poles. With χ = 1 over ℚ and a = 2,
-- the left line passes through the simple pole at -2.

/-- Paper: Theorem 7.4.3.2(2), pp. 372–373.
For tests supported where the norm is greater than one, the quotient operator has
an absolutely convergent matrix trace in every enumeration of the specified
basis of the strong dual. The gamma-pole series is also absolutely convergent.
Deviation: On a trivial norm-one isotype the omitted jet is at the trivial
quasi-character, so its weight is the integral of the test with no character factor. -/
theorem archNuclearity_trace (φ : 𝒟)
    (_hφ : tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)}) :
    let D := archNuclearityDenominator χ
    let Q := Θ₀(χ) ⧸ D
    let poles := {z : ℂ // 0 < gammaOrder(χ, z)}
    let term := fun z : poles ↦ (gammaOrder(χ, z.val) : ℂ) * nuclearityTestMellin χ φ z.val
    let correction := if ω(χ) = 1 then nuclearityTestMellin 1 φ 0 else 0
    ∃ T : Q →L[ℂ] Q,
      (∀ f, T (D.mkQ f) = D.mkQ (Aθ(φ) f)) ∧ Summable (fun z ↦ ‖term z‖) ∧
      ∀ (σ : ℕ ≃ ArchNuclearityJetIndex χ τ hτ) (d : ℕ → StrongDual ℂ Q)
        (b : ℕ → StrongDual ℂ (StrongDual ℂ Q)),
        (∀ n x, d n (D.mkQ x) = archNuclearityJet χ τ hτ (σ n) x) →
        IsSchauderBasis d b →
        let diagonal := fun n ↦ b n ((d n).comp T)
        Summable (fun n ↦ ‖diagonal n‖) ∧ HasSum diagonal ((∑' z, term z) - correction) := by
  intro D Q poles term correction
  obtain ⟨hterm, hσ⟩ := archNuclearity_trace_scalar χ τ hτ φ _hφ
  let M := nuclearityTestMellin χ φ
  have hmaps := (archNuclearityDenominator_closed_invariant χ τ hτ φ).2
  let T₀ : Q →ₗ[ℂ] Q := D.mapQ D (Aθ(φ)).toLinearMap fun x hx ↦ hmaps hx
  have hT₀ : Continuous T₀ := by
    apply (Submodule.isQuotientMap_mkQ D).continuous_iff.mpr
    exact (Submodule.isQuotientMap_mkQ D).continuous.comp (Aθ(φ)).continuous
  let T : Q →L[ℂ] Q := ⟨T₀, hT₀⟩
  have hT (x : Θ₀(χ)) : T (D.mkQ x) = D.mkQ (Aθ(φ) x) := rfl
  refine ⟨T, hT, hterm, ?_⟩
  intro σ d b hd hb diagonal
  have hjet (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ) :
      archNuclearityJet χ τ hτ j x = iteratedDeriv j.val.2 ((Z(χ, τ, hτ)) x).val j.val.1 := by
    unfold archNuclearityJet
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
    exact congrArg (fun g : ℂ → ℂ ↦ iteratedDeriv j.val.2 g j.val.1)
      (funext (schwartzBergmanEntireInclusion_apply _))
  have hjetA (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ) :
      archNuclearityJet χ τ hτ j (Aθ(φ) x) = ∑ i ∈ Finset.range (j.val.2 + 1),
        (j.val.2.choose i : ℂ) * iteratedDeriv i M j.val.1 *
          archNuclearityJet χ τ hτ ⟨(j.val.1, j.val.2 - i),
            (Nat.sub_le _ _).trans_lt j.property⟩ x := by
    let v := (Z(χ, τ, hτ)) x
    have hv : Differentiable ℂ v.val := fun z ↦
      (v.property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    have hprod : ((Z(χ, τ, hτ)) (Aθ(φ) x)).val = M * v.val :=
      funext ((exists_polarThetaNuclearityAction χ τ hτ φ).choose_spec.1 x)
    rw [hjet, hprod, iteratedDeriv_mul
      ((archNuclearityDenominator_closed_invariant_multiplier χ φ).contDiff.contDiffAt)
      hv.contDiff.contDiffAt]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hjet]
  have hdiag (n : ℕ) : diagonal n = M (σ n).val.1 := by
    have h := archNuclearity_trace_diagonal D (Aθ(φ)).toLinearMap T hT
      (archNuclearityMultiplicity χ τ hτ) σ (fun j x ↦ archNuclearityJet χ τ hτ j x)
      (fun i z ↦ iteratedDeriv i M z) M (fun z ↦ by simp) hjetA d b hd (fun m n ↦ hb.1 m n) n
    exact h
  have hdiagfun : diagonal = fun n ↦ M (σ n).val.1 := funext hdiag
  rw [hdiagfun]
  exact hσ σ

/-- A von Neumann bounded set in a space carrying the finest locally convex topology
spans a finite-dimensional subspace: otherwise a linear functional unbounded on it
would be continuous. -/
private theorem archNuclearityStrongDual_finiteRank_bounded {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E]
    (h : (inferInstance : TopologicalSpace E) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex E)))
    (S : Set E) (hS : Bornology.IsVonNBounded ℂ S) :
    FiniteDimensional ℂ (Submodule.span ℂ S) := by
  by_contra hfin
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℂ S
  have hinf : b.Infinite := by
    intro hb
    apply hfin
    rw [← hspan]
    exact FiniteDimensional.span_of_finite ℂ hb
  let f := hinf.natEmbedding
  let v : ℕ → E := fun n ↦ (f n).val
  have hv : LinearIndependent ℂ v := hli.comp f f.injective
  let ℓ₀ : Submodule.span ℂ (Set.range v) →ₗ[ℂ] ℂ :=
    (Finsupp.linearCombination ℂ (fun n : ℕ ↦ (n : ℂ))).comp hv.repr
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  have hℓv (n : ℕ) : ℓ (v n) = n := by
    have h1 := congrArg (fun g ↦ g ⟨v n, Submodule.subset_span ⟨n, rfl⟩⟩) hℓ
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
    rw [h1]
    simp [ℓ₀, hv.repr_eq_single n ⟨v n, Submodule.subset_span ⟨n, rfl⟩⟩ rfl]
  have hcont' : Continuous (show FinestLocallyConvex E →ₗ[ℂ] ℂ from ℓ) := by
    apply WithSeminorms.continuous_normedSpace_rng ℂ (finestLocallyConvex_withSeminorms (E := E))
    refine ⟨{(normSeminorm ℂ ℂ).comp ℓ}, 1, ?_⟩
    rw [one_smul]
    exact Finset.le_sup (f := id) (Finset.mem_singleton_self _)
  have hcont : Continuous ℓ := by
    have : @Continuous E ℂ (inferInstance : TopologicalSpace (FinestLocallyConvex E)) _ ℓ :=
      hcont'
    rwa [← h] at this
  let L : E →L[ℂ] ℂ := ⟨ℓ, hcont⟩
  have hb := (hS.image L)
  rw [NormedSpace.isVonNBounded_iff] at hb
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have := hC (L (v n)) ⟨v n, hbS (f n).property, rfl⟩
  change ‖ℓ (v n)‖ ≤ C at this
  rw [hℓv, Complex.norm_natCast] at this
  linarith

/-- In a Hausdorff space with the finest locally convex topology, an operator with a
nuclear presentation has range inside the span of its Banach disc, which is
finite-dimensional. -/
private theorem archNuclearityStrongDual_finiteRank_gen {E : Type*} [AddCommGroup E]
    [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [ContinuousSMul ℂ E]
    (h : (inferInstance : TopologicalSpace E) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex E)))
    (T : E →L[ℂ] E) (hT : Nonempty (NuclearPresentation T)) :
    FiniteDimensional ℂ T.toLinearMap.range := by
  obtain ⟨r⟩ := hT
  let W := Submodule.span ℂ r.disc
  have hW : FiniteDimensional ℂ W :=
    archNuclearityStrongDual_finiteRank_bounded h r.disc r.isBanachDisc.bounded
  have hWc : IsClosed (W : Set E) := W.isClosed_of_finiteDimensional
  have hle : T.toLinearMap.range ≤ W := by
    rintro _ ⟨x, rfl⟩
    apply hWc.mem_of_tendsto (r.hasSum x)
    filter_upwards with s
    exact W.sum_mem fun n _ ↦ W.smul_mem _ (r.vector n).property
  exact Submodule.finiteDimensional_of_le hle

private theorem archNuclearityStrongDual_finiteRank_dual {Q : Type*} [AddCommGroup Q]
    [Module ℂ Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q] [ContinuousSMul ℂ Q]
    (h : (inferInstance : TopologicalSpace (StrongDual ℂ Q)) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex (StrongDual ℂ Q))))
    (T : StrongDual ℂ Q →L[ℂ] StrongDual ℂ Q) (hT : Nonempty (NuclearPresentation T)) :
    FiniteDimensional ℂ T.toLinearMap.range :=
  archNuclearityStrongDual_finiteRank_gen h T hT

-- Stated over the same tower of quotients as `ArchNuclearityQuotient`, and concluding `FG`,
-- so that applying it to the concrete space needs only syntactic unification (#5398).
private theorem archNuclearityStrongDual_finiteRank_tower {X : Type*} {_ : AddCommGroup X}
    {_ : Module ℂ X} {_ : TopologicalSpace X} [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    (P0 : Submodule ℂ X) (k : Submodule ℂ P0) (p : Submodule ℂ (P0 ⧸ k))
    (h : let E := StrongDual ℂ ((P0 ⧸ k) ⧸ p)
      (inferInstance : TopologicalSpace E) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex E)))
    (T : StrongDual ℂ ((P0 ⧸ k) ⧸ p) →L[ℂ] StrongDual ℂ ((P0 ⧸ k) ⧸ p))
    (hT : Nonempty (NuclearPresentation T)) :
    (LinearMap.range T.toLinearMap).FG :=
  Module.Finite.iff_fg.mp (archNuclearityStrongDual_finiteRank_dual h T hT)

private theorem archNuclearityStrongDual_finiteRank_fd {E : Type*} {_ : AddCommGroup E}
    {_ : Module ℂ E} {S : Submodule ℂ E} (h : S.FG) : FiniteDimensional ℂ S :=
  Module.Finite.iff_fg.mpr h

/-- Paper: Remark 7.4.3.3, p. 373.
Nuclear endomorphisms of the strong dual of the archimedean quotient have finite rank.
Deviation: The printed universal nonnuclearity conclusion needs infinite rank,
which fails for the zero test. -/
theorem archNuclearityStrongDual_finiteRank
    (T : StrongDual ℂ (ArchNuclearityQuotient χ) →L[ℂ] StrongDual ℂ (ArchNuclearityQuotient χ))
    (_hT : Nonempty (NuclearPresentation T)) :
    FiniteDimensional ℂ T.toLinearMap.range :=
  archNuclearityStrongDual_finiteRank_fd
    (archNuclearityStrongDual_finiteRank_tower _ _ _ (archNuclearityStrongDual_finest χ) T _hT)

/-- An equicontinuous family of linear functionals on a sequence space sees only
a common finite set of coordinates. Otherwise rescaled tails tend to zero while
some member of the family still takes the value one. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_tail {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (e : E ≃L[ℂ] (ℕ → ℂ))
    (φ : ℕ → StrongDual ℂ E) (hφ : EquicontinuousAt (fun k x ↦ φ k x) 0) :
    ∃ N : ℕ, ∀ x : E, (∀ j < N, e x j = 0) → ∀ k, φ k x = 0 := by
  by_contra! h
  choose x hx k hk using h
  let y (n : ℕ) : E := (φ (k n) (x n))⁻¹ • x n
  have he : Filter.Tendsto (fun n ↦ e (y n)) Filter.atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro j
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop j] with n hn
    simp [y, hx n j hn]
  have hy : Filter.Tendsto y Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, e.symm_apply_apply, map_zero] using
      (e.symm.continuous.tendsto 0).comp he
  obtain ⟨n, hn⟩ := (hy.eventually (Metric.equicontinuousAt_iff_right.mp hφ 1 one_pos)).exists
  simpa [y, hk n, dist_zero_left] using hn (k n)

/-- A nuclear presentation factors through the finite coordinates detected by its
equicontinuous functionals. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_range {E : Type*}
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [T2Space E]
    [ContinuousSMul ℂ E] (e : E ≃L[ℂ] (ℕ → ℂ)) (T : E →L[ℂ] E) (r : NuclearPresentation T) :
    FiniteDimensional ℂ T.toLinearMap.range := by
  obtain ⟨N, hN⟩ := archNuclearityQuotient_nuclear_iff_finiteRank_tail e r.functional r.equicontinuous
  let a : E →ₗ[ℂ] (Fin N → ℂ) := LinearMap.pi fun j ↦ (LinearMap.proj j.val).comp e.toLinearMap
  have hker : a.ker ≤ T.toLinearMap.ker := by
    intro x hx
    have hφ := hN x fun j hj ↦ congrFun (LinearMap.mem_ker.mp hx) ⟨j, hj⟩
    have hsum := r.hasSum x
    simp only [hφ, mul_zero, zero_smul] at hsum
    exact hsum.unique hasSum_zero
  let : FiniteDimensional ℂ (E ⧸ a.ker) :=
    FiniteDimensional.of_injective a.quotKerEquivRange.toLinearMap a.quotKerEquivRange.injective
  apply FiniteDimensional.of_surjective (a.ker.liftQ T.toLinearMap.rangeRestrict
    (by rwa [LinearMap.ker_rangeRestrict]))
  rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_rangeRestrict]

/-- A map to finitely many complex coordinates has a finite nuclear presentation,
using the coordinate vectors in the closed unit ball. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_coordinates {E : Type*}
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] {d : ℕ} (A : E →L[ℂ] (Fin d → ℂ)) :
    IsNuclearOperator A := by
  classical
  let ball := Metric.closedBall (0 : Fin d → ℂ) 1
  let b (i : Fin d) : Fin d → ℂ := Pi.single i 1
  have hb (i : Fin d) : b i ∈ ball := by simp [ball, b, Metric.mem_closedBall, Pi.norm_single]
  have hz : (0 : Fin d → ℂ) ∈ ball := by simp [ball]
  let c (n : ℕ) : ℂ := if n < d then 1 else 0
  have hc (n : ℕ) (hn : n ∉ Finset.range d) : c n = 0 := ite_eq_right (fun h ↦ hn (Finset.mem_range.mpr h))
  let φ : Option (Fin d) → StrongDual ℂ E := fun i ↦
    i.elim 0 (fun j ↦ (ContinuousLinearMap.proj j).comp A)
  let idx (n : ℕ) : Option (Fin d) := if hn : n < d then some ⟨n, hn⟩ else none
  let y (n : ℕ) : Fin d → ℂ := if hn : n < d then b ⟨n, hn⟩ else 0
  have hy (n : ℕ) : y n ∈ ball := by
    by_cases hn : n < d
    · simpa only [y, dite_eq_left hn] using hb ⟨n, hn⟩
    · simpa only [y, dite_eq_right hn] using hz
  apply (isNuclearOperator_iff_nonempty_presentation A).mpr
  refine ⟨⟨c, fun n ↦ φ (idx n), ball, isBanachDisc_closedUnitBall,
    fun n ↦ ⟨y n, Submodule.subset_span (hy n)⟩, hy, ?_, ?_, fun x ↦ ?_⟩⟩
  · exact (hasSum_sum_of_ne_finset_zero (s := Finset.range d) fun n hn ↦ by
      simp only [hc n hn, norm_zero]).summable
  · exact (equicontinuousAt_finite.mpr (fun i ↦ (φ i).continuous.continuousAt)).comp idx
  · let term (n : ℕ) := (c n * φ (idx n) x) • y n
    have hsum : ∑ n ∈ Finset.range d, term n = A x := by
      rw [← Fin.sum_univ_eq_sum_range term]
      ext j
      simp [term, c, φ, idx, y, b, Pi.single_apply, Finset.sum_apply]
    change HasSum term (A x)
    rw [← hsum]
    exact hasSum_sum_of_ne_finset_zero fun n hn ↦ by simp only [term, hc n hn, zero_mul, zero_smul]

/-- Factor a finite-rank map through coordinates on its range and then include the
range back into the ambient space. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_of_finite {E : Type*}
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] (T : E →L[ℂ] E) (hf : FiniteDimensional ℂ T.toLinearMap.range) :
    Nonempty (NuclearPresentation T) := by
  let b := (Module.finBasis ℂ T.toLinearMap.range).equivFun.toContinuousLinearEquiv
  let A := b.toContinuousLinearMap.comp T.rangeRestrict
  let i := T.toLinearMap.range.subtypeL.comp b.symm.toContinuousLinearMap
  have h := (isNuclearOperator_factor_comps i (Subtype.val_injective.comp b.symm.injective) A
    (archNuclearityQuotient_nuclear_iff_finiteRank_coordinates A)).2
  have he : i.comp A = T := by ext x; exact congrArg Subtype.val (b.symm_apply_apply (T.rangeRestrict x))
  exact (isNuclearOperator_iff_nonempty_presentation T).mp (he ▸ h)

/-- Apply the sequence-space rank criterion with the uniformity of the given
topological additive group. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_sequence {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] (e : E ≃L[ℂ] (ℕ → ℂ)) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    ∀ T : E →L[ℂ] E, Nonempty (NuclearPresentation T) ↔
      FiniteDimensional ℂ T.toLinearMap.range := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : T2Space E := e.symm.toHomeomorph.t2Space
  let : PolynormableSpace ℂ E := e.PolynormableSpace
  intro T
  exact ⟨fun ⟨r⟩ ↦ archNuclearityQuotient_nuclear_iff_finiteRank_range e T r,
    archNuclearityQuotient_nuclear_iff_finiteRank_of_finite T⟩

/-- Paper: Remark 7.4.3.3, p. 373.
A nuclear endomorphism of the archimedean quotient has finite-dimensional range,
and every continuous finite-rank endomorphism admits a nuclear presentation.
Deviation: This gives the rank criterion on the space carrying the test action. -/
theorem archNuclearityQuotient_nuclear_iff_finiteRank :
    let Q := ArchNuclearityQuotient χ
    letI instArchUniformSec4 : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
    ∀ T : Q →L[ℂ] Q, Nonempty (NuclearPresentation T) ↔
      FiniteDimensional ℂ T.toLinearMap.range := by
  obtain ⟨e⟩ := archNuclearityStrongDual_finest_sequenceEquiv χ
  exact archNuclearityQuotient_nuclear_iff_finiteRank_sequence (E := ArchNuclearityQuotient χ) e

/-- In block coordinates, an operator acting on each block by a lower-triangular
Toeplitz matrix with entries `d i z` has values zero on the blocks where all those
entries vanish. -/
private theorem archNuclearityAction_nuclear_iff_vanish {Q : Type*} [AddCommGroup Q]
    [Module ℂ Q] (m : ℂ → ℕ) (d : ℕ → ℂ → ℂ)
    (e : Q ≃ₗ[ℂ] ({j : ℂ × ℕ // j.2 < m j.1} → ℂ)) (T : Q →ₗ[ℂ] Q)
    (hT : ∀ q (j : {j : ℂ × ℕ // j.2 < m j.1}), e (T q) j = ∑ i ∈ Finset.range (j.val.2 + 1),
      (j.val.2.choose i : ℂ) * d i j.val.1 *
        e q ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩)
    (q : Q) (j : {j : ℂ × ℕ // j.2 < m j.1})
    (hj : j.val.1 ∉ {z : ℂ | ∃ k : Fin (m z), d k.val z ≠ 0}) :
    e (T q) j = 0 := by
  rw [hT]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hi' : i < m j.val.1 :=
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans_lt j.property
  have h0 : d i j.val.1 = 0 := by
    by_contra h
    exact hj ⟨⟨i, hi'⟩, h⟩
  rw [h0, mul_zero, zero_mul]

/-- Applying the operator to the first basis vector of the block at `z` gives the
column of entries `d k z` in that block, and zero in the other blocks. -/
private theorem archNuclearityAction_nuclear_iff_column {Q : Type*} [AddCommGroup Q]
    [Module ℂ Q] (m : ℂ → ℕ) (d : ℕ → ℂ → ℂ)
    (e : Q ≃ₗ[ℂ] ({j : ℂ × ℕ // j.2 < m j.1} → ℂ)) (T : Q →ₗ[ℂ] Q)
    (hT : ∀ q (j : {j : ℂ × ℕ // j.2 < m j.1}), e (T q) j = ∑ i ∈ Finset.range (j.val.2 + 1),
      (j.val.2.choose i : ℂ) * d i j.val.1 *
        e q ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩)
    (z : ℂ) (hz : 0 < m z) (j : {j : ℂ × ℕ // j.2 < m j.1}) :
    e (T (e.symm (Pi.single ⟨(z, 0), hz⟩ 1))) j = if j.val.1 = z then d j.val.2 z else 0 := by
  classical
  rw [hT]
  simp only [LinearEquiv.apply_symm_apply]
  split_ifs with hjz
  · rw [Finset.sum_eq_single j.val.2]
    · have : (⟨(j.val.1, j.val.2 - j.val.2), (Nat.sub_le _ _).trans_lt j.property⟩ :
          {j : ℂ × ℕ // j.2 < m j.1}) = ⟨(z, 0), hz⟩ := Subtype.ext (by simp [hjz])
      rw [this, Pi.single_eq_same, mul_one, Nat.choose_self, Nat.cast_one, one_mul, hjz]
    · intro i hi hne
      have hlt : i < j.val.2 :=
        lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
      rw [Pi.single_eq_of_ne, mul_zero]
      intro h
      have := congrArg (fun x : {j : ℂ × ℕ // j.2 < m j.1} ↦ x.val.2) h
      simp only at this
      omega
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [Pi.single_eq_of_ne, mul_zero]
    intro h
    exact hjz (congrArg (fun x : {j : ℂ × ℕ // j.2 < m j.1} ↦ x.val.1) h)

/-- Linear-algebra core of Remark 7.4.3.3: a block lower-triangular operator on the
product of the jet blocks has finite rank exactly when only finitely many blocks
carry a nonzero entry. -/
private theorem archNuclearityAction_nuclear_iff_blocks {Q : Type*} [AddCommGroup Q]
    [Module ℂ Q] (m : ℂ → ℕ) (d : ℕ → ℂ → ℂ)
    (e : Q ≃ₗ[ℂ] ({j : ℂ × ℕ // j.2 < m j.1} → ℂ)) (T : Q →ₗ[ℂ] Q)
    (hT : ∀ q (j : {j : ℂ × ℕ // j.2 < m j.1}), e (T q) j = ∑ i ∈ Finset.range (j.val.2 + 1),
      (j.val.2.choose i : ℂ) * d i j.val.1 *
        e q ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩) :
    FiniteDimensional ℂ (LinearMap.range T) ↔
      {z : ℂ | ∃ k : Fin (m z), d k.val z ≠ 0}.Finite := by
  classical
  let J := {j : ℂ × ℕ // j.2 < m j.1}
  let Z := {z : ℂ | ∃ k : Fin (m z), d k.val z ≠ 0}
  constructor
  · intro hfin
    choose k hk using fun z : Z ↦ z.property
    have hpos (z : Z) : 0 < m z.val := (Nat.zero_le _).trans_lt (k z).isLt
    let w (z : Z) : LinearMap.range T :=
      ⟨T (e.symm (Pi.single ⟨(z.val, 0), hpos z⟩ 1)), LinearMap.mem_range_self _ _⟩
    let Φ : (J → ℂ) →ₗ[ℂ] (Z → ℂ) :=
      LinearMap.pi fun z ↦ LinearMap.proj (⟨(z.val, (k z).val), (k z).isLt⟩ : J)
    let L : LinearMap.range T →ₗ[ℂ] (Z → ℂ) :=
      Φ.comp (e.toLinearMap.comp (LinearMap.range T).subtype)
    have hL (z : Z) : L (w z) = Pi.single z (d (k z).val z.val) := by
      funext z'
      change e (T (e.symm (Pi.single ⟨(z.val, 0), hpos z⟩ 1)))
        ⟨(z'.val, (k z').val), (k z').isLt⟩ = _
      rw [archNuclearityAction_nuclear_iff_column m d e T hT z.val (hpos z)]
      by_cases h : z' = z
      · subst h
        simp
      · have h' : z'.val ≠ z.val := fun he ↦ h (Subtype.ext he)
        simp [h', Pi.single_eq_of_ne h]
    have hli : LinearIndependent ℂ (L ∘ w) := by
      have : L ∘ w = fun z ↦ Pi.single z (d (k z).val z.val) := funext hL
      rw [this]
      exact Pi.linearIndependent_single_of_ne_zero hk
    have := (LinearIndependent.of_comp L hli).finite_of_isNoetherian
    exact Set.toFinite Z
  · intro hZ
    have : Finite Z := hZ.to_subtype
    let JZ := {j : J // j.val.1 ∈ Z}
    have : Finite JZ := by
      refine Finite.of_injective (β := Σ z : Z, Fin (m z.val))
        (fun j ↦ ⟨⟨j.val.val.1, j.property⟩, ⟨j.val.val.2, j.val.property⟩⟩) ?_
      intro a b h
      simp only [Sigma.mk.inj_iff] at h
      obtain ⟨h1, h2⟩ := h
      have h1' : a.val.val.1 = b.val.val.1 := congrArg Subtype.val h1
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext h1' ?_
      have := (Fin.heq_ext_iff (by rw [h1'])).mp h2
      exact this
    let R : LinearMap.range T →ₗ[ℂ] (JZ → ℂ) :=
      (LinearMap.pi fun j : JZ ↦ LinearMap.proj (R := ℂ) (φ := fun _ : J ↦ ℂ) j.val).comp
        (e.toLinearMap.comp (LinearMap.range T).subtype)
    refine Module.Finite.of_injective R ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨_, q, rfl⟩ hx
    apply Subtype.ext
    change T q = 0
    apply e.injective
    funext j
    rw [map_zero, Pi.zero_apply]
    by_cases hj : j.val.1 ∈ Z
    · exact congrFun hx ⟨j, hj⟩
    · exact archNuclearityAction_nuclear_iff_vanish m d e T hT q j hj

/-- Paper: Remark 7.4.3.3, p. 373.
The quotient action is nuclear exactly when it is nonzero on finitely many jet blocks.
Deviation: A block of length m vanishes when all multiplier derivatives of orders
strictly below m vanish at its center. This allows tests whose induced action is zero. -/
theorem archNuclearityAction_nuclear_iff (φ : 𝒟) :
    let D := archNuclearityDenominator χ
    let Q := ArchNuclearityQuotient χ
    letI instArchActionUniformSec4 : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
    ∀ T : Q →L[ℂ] Q, (∀ x : Θ₀(χ), T (D.mkQ x) = D.mkQ (Aθ(φ) x)) →
      (Nonempty (NuclearPresentation T) ↔
        {z : ℂ | ∃ k : Fin (archNuclearityMultiplicity χ τ hτ z),
          iteratedDeriv k.val (nuclearityTestMellin χ φ) z ≠ 0}.Finite) := by
  intro D Q T hT
  obtain ⟨e, he⟩ := archNuclearityQuotient_jetEquiv χ τ hτ
  have hjet (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ) :
      archNuclearityJet χ τ hτ j x = iteratedDeriv j.val.2 ((Z(χ, τ, hτ)) x).val j.val.1 := by
    unfold archNuclearityJet
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
    exact congrArg (fun g : ℂ → ℂ ↦ iteratedDeriv j.val.2 g j.val.1)
      (funext (schwartzBergmanEntireInclusion_apply _))
  have hblock (q : Q) (j : ArchNuclearityJetIndex χ τ hτ) :
      e (T q) j = ∑ i ∈ Finset.range (j.val.2 + 1),
        (j.val.2.choose i : ℂ) * iteratedDeriv i (nuclearityTestMellin χ φ) j.val.1 *
          e q ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩ := by
    obtain ⟨x, rfl⟩ := D.mkQ_surjective q
    let v := (Z(χ, τ, hτ)) x
    have hv : Differentiable ℂ v.val := fun z ↦
      (v.property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    have hprod : ((Z(χ, τ, hτ)) (Aθ(φ) x)).val = nuclearityTestMellin χ φ * v.val :=
      funext ((exists_polarThetaNuclearityAction χ τ hτ φ).choose_spec.1 x)
    rw [hT x, he, hjet, hprod, iteratedDeriv_mul
      ((archNuclearityDenominator_closed_invariant_multiplier χ φ).contDiff.contDiffAt)
      hv.contDiff.contDiffAt]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [he, hjet]
  rw [archNuclearityQuotient_nuclear_iff_finiteRank χ T]
  exact archNuclearityAction_nuclear_iff_blocks (archNuclearityMultiplicity χ τ hτ)
    (fun i z ↦ iteratedDeriv i (nuclearityTestMellin χ φ) z) e.toLinearEquiv T.toLinearMap hblock

end Archimedean

end RiemannMasullo

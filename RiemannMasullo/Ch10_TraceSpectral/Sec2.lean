module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
import RiemannMasullo.ForMathlib.Analysis.Complex.Blaschke
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.Total
import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactGroup
import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import RiemannMasullo.ForMathlib.Analysis.Complex.BlaschkeFactorization
import RiemannMasullo.ForMathlib.Analysis.Complex.StripReciprocal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.ChangeVariables
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.NormedSpace
import RiemannMasullo.External.TauCeti.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Measure.Prod
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzJetClosure
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Roots
import all RiemannMasullo.Ch09_HardySobolev.Sec2
import all RiemannMasullo.Ch09_HardySobolev.Sec3

/-!
# Spectral Markushevich bases

Masullo, §10.2, pp. 438–447. The basis vectors in the negative spaces are
represented by functions modulo almost-everywhere equality.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (logIdeleClassNorm F)
local notation "W(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s
local notation "W'(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s true
local notation "Θ(" a ", " hI ", " hs ")" => globalThetaSobolev F a hI hs
local notation "ρ(" l ", " r ", " s ", " hI ", " hs ")" =>
  (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).comp (ideleClassNorm F).ker.subtype
local notation "Wω(" hI ", " hs ", " ω ")" => actionIsotype (ρ(_, _, _, hI, hs)) ω
local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)

local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "hms𝔽" => (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1

section Quotients

/-- Paper: (10.2.1.1), p. 439, and (10.2.2.1), p. 445. The denominator is the
closed subspace from §10.1, giving the canonical norm on the quotient. -/
instance instClosedSpectralThetaSec2 (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :
    IsClosed (Θ(a, hI, hs) : Set W(l, r, s)) :=
  Submodule.isClosed_topologicalClosure _

/-- Paper: (10.2.1.2), p. 439, and (10.2.2.2), p. 445. The numerator of the
isotype quotient is a closed subspace of the ambient Hilbert space. -/
instance instClosedSpectralIsotypeSec2 {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) : IsClosed (Wω(hI, hs, ω) : Set W(l, r, s)) :=
  isClosed_actionIsotype (ρ(l, r, s, hI, hs)) ω

/-- Paper: (10.2.1.2), p. 439, and (10.2.2.2), p. 445. The isotype quotient
uses the closed intersection of the isotype with the theta subspace. -/
instance instClosedSpectralIsotypeThetaSec2 (a : ℝ) {l r s : ℝ} (hI : l ≤ r)
    (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    IsClosed ((Θ(a, hI, hs)).comap (Wω(hI, hs, ω)).subtype : Set ↥(Wω(hI, hs, ω))) :=
  (instClosedSpectralThetaSec2 (F := F) a hI hs).preimage continuous_subtype_val

variable (F) in
/-- Paper: (10.2.1.1), p. 439, and (10.2.2.1), p. 445. Divide the weighted
Sobolev space by the closure of the weighted polar-free theta functions.
Deviation: The line uses the compact interval with both endpoints zero, as in §9.2.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev spectralSobolevQuotient (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :=
  W(l, r, s) ⧸ Θ(a, hI, hs)

/-- Paper: (10.2.1.1), p. 439, and (10.2.2.1), p. 445. A Sobolev vector has
zero spectral class exactly when it is in the closed weighted theta subspace. -/
theorem spectralSobolevQuotient_eq_zero (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (f : W(l, r, s)) : Θ(a, hI, hs).mkQ f = 0 ↔ f ∈ Θ(a, hI, hs) :=
  Submodule.Quotient.mk_eq_zero _

variable (F) in
/-- Paper: (10.2.1.2), p. 439, and (10.2.2.2), p. 445. Divide the ambient
norm-one isotype by its closed weighted theta subspace. -/
def spectralSobolevIsotypeQuotient (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :=
  ↥(Wω(hI, hs, ω)) ⧸ (Θ(a, hI, hs)).comap (Wω(hI, hs, ω)).subtype

section IsotypeQuotient

variable (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)

local notation "Nω(" ω ")" => (Θ(a, hI, hs)).comap (Wω(hI, hs, ω)).subtype

/-- The isotype quotient carries the quotient norm. -/
instance instNormedAddCommGroupSpectralSobolevIsotypeQuotient (ω : PontryaginDual C₁) :
    NormedAddCommGroup (spectralSobolevIsotypeQuotient F a hI hs ω) :=
  inferInstanceAs (NormedAddCommGroup (↥(Wω(hI, hs, ω)) ⧸ Nω(ω)))

/-- The closed isotypic theta subspace gives the quotient its complex inner product. -/
instance instInnerProductSpaceSpectralSobolevIsotypeQuotient (ω : PontryaginDual C₁) :
    InnerProductSpace ℂ (spectralSobolevIsotypeQuotient F a hI hs ω) :=
  inferInstanceAs (InnerProductSpace ℂ (↥(Wω(hI, hs, ω)) ⧸ Nω(ω)))

/-- The quotient of the closed Sobolev isotype is complete. -/
instance instCompleteSpaceSpectralSobolevIsotypeQuotient (ω : PontryaginDual C₁) :
    CompleteSpace (spectralSobolevIsotypeQuotient F a hI hs ω) :=
  inferInstanceAs (CompleteSpace (↥(Wω(hI, hs, ω)) ⧸ Nω(ω)))

/-- The continuous linear map sending an isotypic Sobolev vector to its spectral class. -/
def spectralSobolevIsotypeQuotient_mk (ω : PontryaginDual C₁) :
    Wω(hI, hs, ω) →L[ℂ] spectralSobolevIsotypeQuotient F a hI hs ω :=
  (Nω(ω)).mkQL

/-- An isotypic vector has zero spectral class exactly when it belongs to the theta subspace. -/
theorem spectralSobolevIsotypeQuotient_mk_eq_zero_iff (ω : PontryaginDual C₁) (f : Wω(hI, hs, ω)) :
    spectralSobolevIsotypeQuotient_mk a hI hs ω f = 0 ↔ f.val ∈ Θ(a, hI, hs) :=
  Submodule.Quotient.mk_eq_zero (Nω(ω))

/-- Every spectral class has an isotypic Sobolev representative. -/
theorem spectralSobolevIsotypeQuotient_mk_surjective (ω : PontryaginDual C₁) :
    Surjective (spectralSobolevIsotypeQuotient_mk (F := F) a hI hs ω) :=
  (Nω(ω)).mkQ_surjective

end IsotypeQuotient

/-- Testing an isotypic Pettis average against a functional gives its scalar integral. -/
private theorem spectralSobolevIsotypeQuotient_isometry_dual {K W : Type*} [Group K]
    [TopologicalSpace K] [MeasurableSpace K] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (μ : Measure K) (ρ : K →* (W →L[ℂ] W)) (ω : PontryaginDual K) (P : W →L[ℂ] W)
    (hP : IsPettisIsotypicAverageOn μ univ ρ ω P) (u : W) (φ : StrongDual ℂ W) :
    φ (P u) = ∫ k, star (ω k : ℂ) * φ (ρ k u) ∂μ := by
  obtain ⟨_, he⟩ := hP u
  have h := congrArg (fun z : PettisWeakCompletion W ↦
    (show Module.Dual ℂ (StrongDual ℂ W) from z) φ) he
  change φ (P u) = ∫ g, φ (star (ω g : ℂ) • ρ g u) ∂μ.restrict univ at h
  simpa only [Measure.restrict_univ, map_smul, smul_eq_mul] using h

/-- A unit complex number times its conjugate is one. -/
private theorem spectralSobolevIsotypeQuotient_isometry_star_mul {K : Type*} [Group K]
    [TopologicalSpace K] (ω : PontryaginDual K) (k : K) :
    star (ω k : ℂ) * (ω k : ℂ) = 1 := by
  rw [Complex.star_def, Complex.conj_mul', Circle.norm_coe]
  simp

/-- The isotypic average descends to a quotient by an invariant subspace. -/
private theorem spectralSobolevIsotypeQuotient_isometry_quot {G W : Type*} [Group G]
    (K : Subgroup G) [TopologicalSpace K] [MeasurableSpace K]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (ρ : G →* (W →L[ℂ] W))
    (N : Submodule ℂ W) [IsClosed (N : Set W)] (ω : PontryaginDual K) (μ : Measure K)
    (P : W →L[ℂ] W) (hP : IsPettisIsotypicAverageOn μ univ (ρ.comp K.subtype) ω P)
    (u : W) (ψ : StrongDual ℂ (W ⧸ N)) :
    ψ (N.mkQ (P u)) = ∫ k, star (ω k : ℂ) * ψ (N.mkQ (ρ k u)) ∂μ :=
  spectralSobolevIsotypeQuotient_isometry_dual μ (ρ.comp K.subtype) ω P hP u
    (ψ.comp N.mkQL)

/-- On the isotype the average is multiplication by the total mass. -/
private theorem spectralSobolevIsotypeQuotient_isometry_fix {G W : Type*} [Group G]
    (K : Subgroup G) [TopologicalSpace K] [MeasurableSpace K]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (ρ : G →* (W →L[ℂ] W))
    (ω : PontryaginDual K) (μ : Measure K) (P : W →L[ℂ] W)
    (hP : IsPettisIsotypicAverageOn μ univ (ρ.comp K.subtype) ω P)
    {u : W} (hu : u ∈ actionIsotype (ρ.comp K.subtype) ω) :
    P u = (μ.real univ : ℂ) • u := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro φ
  rw [spectralSobolevIsotypeQuotient_isometry_dual μ (ρ.comp K.subtype) ω P hP u φ]
  have hu' := (mem_actionIsotype _ _ _).1 hu
  have h (k : K) : star (ω k : ℂ) * φ ((ρ.comp K.subtype) k u) = φ u := by
    rw [hu' k, map_smul, smul_eq_mul, ← mul_assoc,
      spectralSobolevIsotypeQuotient_isometry_star_mul, one_mul]
  simp only [h, integral_const, map_smul, Complex.real_smul, smul_eq_mul]

/-- The average is bounded by the mass when the subgroup acts by contractions. -/
private theorem spectralSobolevIsotypeQuotient_isometry_norm {G W : Type*} [Group G]
    (K : Subgroup G) [TopologicalSpace K] [MeasurableSpace K]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (ρ : G →* (W →L[ℂ] W))
    (hK : ∀ (k : K) (u : W), ‖ρ k u‖ ≤ ‖u‖)
    (ω : PontryaginDual K) (μ : Measure K) [IsFiniteMeasure μ] (P : W →L[ℂ] W)
    (hP : IsPettisIsotypicAverageOn μ univ (ρ.comp K.subtype) ω P) (u : W) :
    ‖P u‖ ≤ μ.real univ * ‖u‖ := by
  obtain ⟨g, hg, hgu⟩ := exists_dual_vector'' ℂ (P u)
  have h1 : g (P u) = ∫ k, star (ω k : ℂ) * g ((ρ.comp K.subtype) k u) ∂μ :=
    spectralSobolevIsotypeQuotient_isometry_dual μ (ρ.comp K.subtype) ω P hP u g
  have h3 : ‖g (P u)‖ = ‖P u‖ := by rw [hgu]; simp
  have h2 : ‖∫ k, star (ω k : ℂ) * g ((ρ.comp K.subtype) k u) ∂μ‖ ≤ ‖u‖ * μ.real univ := by
    apply norm_integral_le_of_norm_le_const
    refine ae_of_all _ fun k ↦ ?_
    rw [norm_mul, norm_star, Circle.norm_coe, one_mul]
    exact (g.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hg).trans (hK k u))
  rw [← h1, h3] at h2
  linarith

/-- The average maps an invariant closed subspace into itself. -/
private theorem spectralSobolevIsotypeQuotient_isometry_mem {G W : Type*} [Group G]
    (K : Subgroup G) [TopologicalSpace K] [MeasurableSpace K]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (ρ : G →* (W →L[ℂ] W))
    (N : Submodule ℂ W) [IsClosed (N : Set W)] (hN : ∀ g, ∀ n ∈ N, ρ g n ∈ N)
    (ω : PontryaginDual K) (μ : Measure K) (P : W →L[ℂ] W)
    (hP : IsPettisIsotypicAverageOn μ univ (ρ.comp K.subtype) ω P) {n : W} (hn : n ∈ N) :
    P n ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero]
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro ψ
  have h := spectralSobolevIsotypeQuotient_isometry_quot K ρ N ω μ P hP n ψ
  have h0 (k : K) : N.mkQ (ρ k n) = 0 := (Submodule.Quotient.mk_eq_zero N).2 (hN _ n hn)
  simp only [h0, map_zero, mul_zero, integral_zero] at h
  simpa using h

/-- On the quotient, the average of a class in the quotient isotype is the mass times it. -/
private theorem spectralSobolevIsotypeQuotient_isometry_quotFix {G W : Type*} [Group G]
    (K : Subgroup G) [TopologicalSpace K] [MeasurableSpace K]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (ρ : G →* (W →L[ℂ] W))
    (N : Submodule ℂ W) [IsClosed (N : Set W)]
    (ω : PontryaginDual K) (μ : Measure K) (P : W →L[ℂ] W)
    (hP : IsPettisIsotypicAverageOn μ univ (ρ.comp K.subtype) ω P) {f : W}
    (hf : ∀ k : K, N.mkQ (ρ k f) = (ω k : ℂ) • N.mkQ f) :
    N.mkQ (P f) = (μ.real univ : ℂ) • N.mkQ f := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro ψ
  rw [spectralSobolevIsotypeQuotient_isometry_quot K ρ N ω μ P hP f ψ]
  have h (k : K) : star (ω k : ℂ) * ψ (N.mkQ (ρ k f)) = ψ (N.mkQ f) := by
    rw [hf k, map_smul, smul_eq_mul, ← mul_assoc,
      spectralSobolevIsotypeQuotient_isometry_star_mul, one_mul]
  simp only [h, integral_const, map_smul, Complex.real_smul, smul_eq_mul]

/-- Abstract form of `spectralSobolevIsotypeQuotient_isometry`: an action preserving a
closed subspace descends to the quotient, and if a compact subgroup acts by contractions
with an isotypic average, the isotype quotient is isometric to the isotype of the quotient. -/
private theorem spectralSobolevIsotypeQuotient_isometry_abstract {G W : Type*} [Group G]
    [TopologicalSpace G] (K : Subgroup G) [TopologicalSpace K] [MeasurableSpace K]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (ρ : G →* (W →L[ℂ] W))
    (hρ : Continuous fun p : G × W ↦ ρ p.1 p.2)
    (N : Submodule ℂ W) [IsClosed (N : Set W)] (hN : ∀ g, ∀ n ∈ N, ρ g n ∈ N)
    (hK : ∀ (k : K) (u : W), ‖ρ k u‖ ≤ ‖u‖)
    (ω : PontryaginDual K) (μ : Measure K) [IsFiniteMeasure μ] (hμ : μ univ ≠ 0)
    (A : W →L[ℂ] actionIsotype (ρ.comp K.subtype) ω)
    (hA : IsPettisIsotypicAverageOn μ univ (ρ.comp K.subtype) ω
      ((actionIsotype (ρ.comp K.subtype) ω).subtypeL.comp A))
    [IsClosed ((N.comap (actionIsotype (ρ.comp K.subtype) ω).subtype) :
      Set (actionIsotype (ρ.comp K.subtype) ω))] :
    ∃ ρQ : G →* ((W ⧸ N) →L[ℂ] (W ⧸ N)),
      (∀ g f, ρQ g (N.mkQ f) = N.mkQ (ρ g f)) ∧
      Continuous (fun p : G × (W ⧸ N) ↦ ρQ p.1 p.2) ∧
      ∃ U : (↥(actionIsotype (ρ.comp K.subtype) ω) ⧸
          N.comap (actionIsotype (ρ.comp K.subtype) ω).subtype) ≃ₗᵢ[ℂ]
          actionIsotype (ρQ.comp K.subtype) ω,
        ∀ f : actionIsotype (ρ.comp K.subtype) ω,
          (U ((N.comap (actionIsotype (ρ.comp K.subtype) ω).subtype).mkQ f) : W ⧸ N) =
            N.mkQ f.val := by
  let E := actionIsotype (ρ.comp K.subtype) ω
  let M := N.comap E.subtype
  let P : W →L[ℂ] W := E.subtypeL.comp A
  let c : ℝ := μ.real univ
  have hc : 0 < c := ENNReal.toReal_pos hμ (measure_ne_top μ univ)
  have hker (g : G) : N ≤ (N.mkQL.comp (ρ g)).ker := fun n hn ↦
    (Submodule.Quotient.mk_eq_zero N).2 (hN g n hn)
  let T (g : G) : (W ⧸ N) →L[ℂ] (W ⧸ N) := N.liftQL (N.mkQL.comp (ρ g)) (hker g)
  have hT (g : G) (f : W) : T g (N.mkQ f) = N.mkQ (ρ g f) := rfl
  let ρQ : G →* ((W ⧸ N) →L[ℂ] (W ⧸ N)) :=
    { toFun := T
      map_one' := by
        refine ContinuousLinearMap.ext fun x ↦ ?_
        obtain ⟨f, rfl⟩ := N.mkQ_surjective x
        change T 1 (N.mkQ f) = N.mkQ f
        rw [hT, map_one, one_apply_eq_self]
      map_mul' := fun g h ↦ by
        refine ContinuousLinearMap.ext fun x ↦ ?_
        obtain ⟨f, rfl⟩ := N.mkQ_surjective x
        change T (g * h) (N.mkQ f) = T g (T h (N.mkQ f))
        rw [hT, hT, hT, map_mul, mul_apply_eq_comp] }
  have hρQ (g : G) (f : W) : ρQ g (N.mkQ f) = N.mkQ (ρ g f) := rfl
  refine ⟨ρQ, hρQ, ?_, ?_⟩
  · have hq : IsOpenQuotientMap (Prod.map id N.mkQ : G × W → G × (W ⧸ N)) :=
      IsOpenQuotientMap.id.prodMap N.isOpenQuotientMap_mkQL
    rw [hq.isQuotientMap.continuous_iff]
    exact N.mkQL.continuous.comp hρ
  -- the isometry
  have hmemQ (f : E) : N.mkQ (f : W) ∈ actionIsotype (ρQ.comp K.subtype) ω := by
    refine (mem_actionIsotype _ _ _).2 fun k ↦ ?_
    change ρQ k (N.mkQ (f : W)) = _
    rw [hρQ, show ρ k (f : W) = (ω k : ℂ) • (f : W) from (mem_actionIsotype _ _ _).1 f.2 k,
      map_smul]
  let L₀ : E →ₗ[ℂ] actionIsotype (ρQ.comp K.subtype) ω :=
    LinearMap.codRestrict _ (N.mkQ ∘ₗ E.subtype) hmemQ
  have hL₀ : M ≤ LinearMap.ker L₀ := fun f hf ↦ by
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero N).2 hf
  let L : (E ⧸ M) →ₗ[ℂ] actionIsotype (ρQ.comp K.subtype) ω := M.liftQ L₀ hL₀
  have hL (f : E) : (L (M.mkQ f) : W ⧸ N) = N.mkQ (f : W) := rfl
  -- the projection `c⁻¹ • A` onto `E`
  have hfix (f : E) : P f = (c : ℂ) • (f : W) :=
    spectralSobolevIsotypeQuotient_isometry_fix K ρ ω μ P hA f.2
  have hnorm (w : W) : ‖P w‖ ≤ c * ‖w‖ :=
    spectralSobolevIsotypeQuotient_isometry_norm K ρ hK ω μ P hA w
  let B (w : W) : E := (c⁻¹ : ℂ) • A w
  have hB (f : E) (w : W) (hw : N.mkQ w = N.mkQ (f : W)) : M.mkQ (B w) = M.mkQ f := by
    apply (Submodule.Quotient.eq M).2
    change ((c⁻¹ : ℂ) • P w - (f : W)) ∈ N
    have h1 : w - (f : W) ∈ N := (Submodule.Quotient.eq N).1 hw
    have h2 := spectralSobolevIsotypeQuotient_isometry_mem K ρ N hN ω μ P hA h1
    rw [map_sub, hfix f] at h2
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    convert N.smul_mem (c⁻¹ : ℂ) h2 using 1
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hc', one_smul]
  have hBn (w : W) : ‖B w‖ ≤ ‖w‖ := by
    change ‖(c⁻¹ : ℂ) • P w‖ ≤ ‖w‖
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le]
    calc c⁻¹ * ‖P w‖ ≤ c⁻¹ * (c * ‖w‖) := by gcongr; exact hnorm w
      _ = ‖w‖ := by field_simp
  have hiso (x : E ⧸ M) : ‖L x‖ = ‖x‖ := by
    obtain ⟨f, rfl⟩ := M.mkQ_surjective x
    change ‖N.mkQ (f : W)‖ = ‖M.mkQ f‖
    apply le_antisymm
    · refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
      obtain ⟨m, hm, hmε⟩ := Submodule.Quotient.norm_mk_lt (M.mkQ f) hε
      have hmN : N.mkQ (m : W) = N.mkQ (f : W) := by
        apply (Submodule.Quotient.eq N).2
        exact (Submodule.Quotient.eq M).1 hm
      rw [← hmN]
      exact (Submodule.Quotient.norm_mk_le N (m : W)).trans_lt hmε
    · refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
      obtain ⟨w, hw, hwε⟩ := Submodule.Quotient.norm_mk_lt (N.mkQ (f : W)) hε
      rw [← hB f w hw]
      exact ((Submodule.Quotient.norm_mk_le M (B w)).trans (hBn w)).trans_lt hwε
  have hsurj : Surjective L := by
    rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := N.mkQ_surjective y
    refine ⟨M.mkQ (B w), Subtype.ext ?_⟩
    rw [hL]
    change N.mkQ ((c⁻¹ : ℂ) • P w) = N.mkQ w
    have hw : ∀ k : K, N.mkQ (ρ k w) = (ω k : ℂ) • N.mkQ w := fun k ↦
      (mem_actionIsotype _ _ _).1 hy k
    rw [map_smul, spectralSobolevIsotypeQuotient_isometry_quotFix K ρ N ω μ P hA hw, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hc.ne'), one_smul]
  exact ⟨LinearIsometryEquiv.ofSurjective ⟨L, hiso⟩ hsurj, fun f ↦ rfl⟩

/-- Paper: (10.2.1.2), p. 439, and (10.2.2.2), p. 445. The isotype quotient
maps isometrically onto the isotype of the full quotient by inclusion of
representatives. The isotype action is the restriction of the continuous
idele class group action on that quotient. -/
theorem spectralSobolevIsotypeQuotient_isometry (a : ℝ) {l r s : ℝ} (hI : l ≤ r)
    (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    let N := Θ(a, hI, hs)
    let Q := spectralSobolevQuotient F a hI hs
    let E := Wω(hI, hs, ω)
    ∃ ρQ : C𝔽 →* (Q →L[ℂ] Q),
      (∀ (g : C𝔽) (f : W(l, r, s)),
        ρQ g (N.mkQ f) = N.mkQ (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs g f)) ∧
      Continuous (fun p : C𝔽 × Q ↦ ρQ p.1 p.2) ∧
      ∃ U : spectralSobolevIsotypeQuotient F a hI hs ω ≃ₗᵢ[ℂ]
          actionIsotype (ρQ.comp (ideleClassNorm F).ker.subtype) ω,
        ∀ f : E, (U ((N.comap E.subtype).mkQ f) : Q) = N.mkQ f.val := by
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hρ := (exists_hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).choose_spec.2
  have hA := (existsUnique_thetaSobolevAverage_of_compact (ideleClassNorm F).ker
    (normOneIdeleClassTamagawaMeasure F) (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs) hρ
    ω).exists
  have hR := (exists_globalThetaSobolevAction (F := F) a hI hs).choose_spec.1
  have hN (g : C𝔽) (n : W(l, r, s)) (hn : n ∈ Θ(a, hI, hs)) :
      hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs g n ∈ Θ(a, hI, hs) := by
    rw [← hR g ⟨n, hn⟩]
    exact (_ : ↥(Θ(a, hI, hs))).2
  have hK (k : C₁) (u : W(l, r, s)) :
      ‖hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs k u‖ ≤ ‖u‖ := by
    have h1 : ((m𝔽 (k : C𝔽)).val : ℝ) = 1 := by
      have h : ideleClassNorm F (k : C𝔽) = 1 := k.2
      change (((ideleClassNorm F (k : C𝔽)).val : ℝ≥0) : ℝ) = 1
      rw [h]
      rfl
    have h := norm_hardySobolevTranslation_le μ𝔽 m𝔽 l r s hI hs (k : C𝔽)
    simp only [h1, Real.log_one, mul_zero, Real.exp_zero, max_self, abs_zero, add_zero,
      Real.one_rpow, mul_one] at h
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) h)
  have hμ : normOneIdeleClassTamagawaMeasure F univ ≠ 0 :=
    isOpen_univ.measure_ne_zero _ univ_nonempty
  exact spectralSobolevIsotypeQuotient_isometry_abstract (ideleClassNorm F).ker
    (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs) hρ (Θ(a, hI, hs)) hN hK ω
    (normOneIdeleClassTamagawaMeasure F) hμ hA.choose hA.choose_spec.1

/-- Paper: (10.2.1.3), pp. 439–440, and (10.2.2.3), p. 445. The Sobolev
duality evaluates the unweighted bilinear product integral. -/
def spectralSobolevPairing {l r s : ℝ} (f : W(l, r, s)) (u : W'(l, r, s)) : ℂ :=
  ∫ g, f g * u g ∂μ𝔽

local notation "pair(" f ", " u ")" => spectralSobolevPairing (F := F) f u

local notation "T(" l ", " r ", " s ", " hI ", " hs ")" =>
  (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 l r s hI hs).exists.choose

/-- Paper: (10.2.1.3), p. 440, and (10.2.2.3), p. 445. The pairing is
integrable and evaluates the ambient strong dual under its Sobolev isometry. -/
theorem spectralSobolevPairing_dual {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (Λ : StrongDual ℂ W(l, r, s)) (f : W(l, r, s)) :
    let T := T(l, r, s, hI, hs)
    Integrable (fun g ↦ f g * T Λ g) μ𝔽 ∧ Λ f = pair(f, T Λ) := by
  exact (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 l r s hI hs).exists.choose_spec Λ f

/-- Conjugating a weighted L² vector and multiplying by the density gives a vector of the
reciprocal-weight space whose product integral with the original is its squared norm. -/
private theorem spectralSobolevPairing_isotype_conj {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {ρ ρ' : X → ℝ} (hρ : Measurable ρ) (hρ' : Measurable ρ') (hpos : ∀ x, 0 < ρ x)
    (hpos' : ∀ x, 0 < ρ' x) (hr : ∀ x, ρ x * ρ' x = 1)
    (f : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x))) :
    ∃ g : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)),
      (g : X → ℂ) =ᵐ[ν] (fun x ↦ (ρ x : ℂ) * star (f x)) ∧
      ∫ x, f x * g x ∂ν = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
  have hbase {ρ : X → ℝ} (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x) :
      ν ≪ ν.withDensity fun x ↦ ENNReal.ofReal (ρ x) :=
    withDensity_absolutelyContinuous' hρ.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  let u : X → ℂ := fun x ↦ (ρ x : ℂ) * star (f x)
  have hsq (x : X) : ‖u x‖ ^ 2 * ρ' x = ‖f x‖ ^ 2 * ρ x := by
    calc
      _ = ‖f x‖ ^ 2 * (ρ x * (ρ x * ρ' x)) := by
        dsimp only [u]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos x), norm_star]
        ring
      _ = _ := by rw [hr, mul_one]
  have hmeas : AEStronglyMeasurable u (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)) :=
    (Complex.measurable_ofReal.comp hρ).aestronglyMeasurable.mul
      (((Lp.aestronglyMeasurable f).mono_ac (hbase hρ hpos)).mono_ac
        (withDensity_absolutelyContinuous _ _)).star
  have hmem : MemLp u 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)) := by
    apply (memLp_two_iff_integrable_sq_norm hmeas).2
    apply (integrable_withDensity_iff hρ'.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
    refine (weightedL2_norm_eq ν hρ hpos f).1.congr (ae_of_all _ fun x ↦ ?_)
    change ‖f x‖ ^ 2 * ρ x = ‖u x‖ ^ 2 * (ENNReal.ofReal (ρ' x)).toReal
    rw [ENNReal.toReal_ofReal (hpos' x).le, hsq]
  have hcoe : (hmem.toLp u : X → ℂ) =ᵐ[ν] u := (hbase hρ' hpos').ae_eq hmem.coeFn_toLp
  refine ⟨hmem.toLp u, hcoe, ?_⟩
  obtain ⟨hint, hnorm⟩ := weightedL2_norm_eq ν hρ hpos f
  have hI : ∫ x, ‖f x‖ ^ 2 * ρ x ∂ν = ‖f‖ ^ 2 := by
    rw [hnorm, Real.sq_sqrt (integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _) (hpos x).le)]
  rw [← hI, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with x hx
  rw [hx]
  dsimp only [u]
  rw [Complex.star_def, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj']
  ring

/-- Paper: (10.2.1.3), p. 440, and (10.2.2.3), p. 445. The pairing on a
positive Sobolev isotype and the conjugate reciprocal-weight isotype is nondegenerate.
The negative-space isotype is specified by left translation of its representatives. -/
theorem spectralSobolevPairing_isotype {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    let IsConjugate (u : W'(l, r, s)) :=
      ∀ k : C₁, (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω⁻¹ k : ℂ) * u g
    (∀ f : Wω(hI, hs, ω), f ≠ 0 →
      ∃ u : W'(l, r, s), IsConjugate u ∧ pair(f.val, u) ≠ 0) ∧
    ∀ u : W'(l, r, s), IsConjugate u → u ≠ 0 →
      ∃ f : Wω(hI, hs, ω), pair(f.val, u) ≠ 0 := by
  intro IsConjugate
  let w : C𝔽 → ℝ := fun g ↦ intervalSobolevDensity l r s (logNorm g)
  have hlog : Measurable logNorm :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm F).continuous)).measurable.log
  have hw : Measurable w := (continuous_intervalSobolevDensity' l r s).measurable.comp hlog
  have hwpos : ∀ x, 0 < w x := fun x ↦ intervalSobolevDensity_pos l r s _
  have hwk : ∀ (k : C₁) g, w (k.val⁻¹ * g) = w g := by
    intro k g
    have hk : ideleClassNorm F k.val = 1 := k.2
    simp only [w, logIdeleClassNorm, map_mul, map_inv, hk, inv_one, one_mul]
  have hbase : μ𝔽 ≪ (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (w x)) :=
    withDensity_absolutelyContinuous' hw.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hwpos x)).ne')
  have hwd : ((μ𝔽).withDensity fun x ↦ ENNReal.ofReal (w x)) ≪ μ𝔽 :=
    withDensity_absolutelyContinuous _ _
  have hiso (f : W(l, r, s)) : f ∈ Wω(hI, hs, ω) ↔
      ∀ k : C₁, (fun g ↦ f (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω k : ℂ) * f g := by
    rw [mem_actionIsotype]
    refine forall_congr' fun k ↦ ?_
    have htr := hardySobolevTranslation_apply μ𝔽 m𝔽 l r s hI hs k.val f
    have hsm := hbase.ae_eq (Lp.coeFn_smul (ω k : ℂ) f)
    change hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs k.val f = (ω k : ℂ) • f ↔ _
    constructor
    · intro h
      rw [h] at htr
      exact htr.symm.trans hsm
    · intro h
      exact Lp.ext (hwd.ae_eq (htr.trans (h.trans hsm.symm)))
  have hωinv (k : C₁) : ((ω⁻¹ k : Circle) : ℂ) = star (ω k : ℂ) := by
    rw [show ω⁻¹ k = (ω k)⁻¹ from rfl, Circle.coe_inv_eq_conj]
    rfl
  have hqmp (k : C₁) := (measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving
  refine ⟨fun f hf ↦ ?_, fun u hu hu0 ↦ ?_⟩
  · obtain ⟨u, hu, hpair⟩ : ∃ u : W'(l, r, s),
        (u : C𝔽 → ℂ) =ᵐ[μ𝔽] (fun x ↦ (w x : ℂ) * star (f.val x)) ∧
        ∫ x, f.val x * u x ∂μ𝔽 = ((‖f.val‖ ^ 2 : ℝ) : ℂ) :=
      spectralSobolevPairing_isotype_conj μ𝔽 (ρ := w) (ρ' := fun x ↦ (w x)⁻¹) hw hw.inv hwpos
        (fun x ↦ inv_pos.2 (hwpos x)) (fun x ↦ mul_inv_cancel₀ (hwpos x).ne') f.val
    refine ⟨u, fun k ↦ ?_, ?_⟩
    · have hfk := (hiso f.val).1 f.2 k
      have hu' := (hqmp k).ae_eq_comp hu
      filter_upwards [hu', hfk, hu] with g h1 h2 h3
      simp only [comp_apply] at h1
      rw [h1, h2, h3, hwk, star_mul']
      simp only [hωinv]
      ring
    · change ∫ g, f.val g * u g ∂μ𝔽 ≠ 0
      rw [hpair]
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 fun h ↦ hf (Subtype.ext h))
  · have key : ∃ f : W(l, r, s),
        (f : C𝔽 → ℂ) =ᵐ[μ𝔽] (fun x ↦ ((w x)⁻¹ : ℂ) * star (u x)) ∧
        ∫ x, u x * f x ∂μ𝔽 = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      obtain ⟨f, hf, hpair⟩ := spectralSobolevPairing_isotype_conj μ𝔽
        (ρ := fun x ↦ if true = true then (w x)⁻¹ else w x)
        (ρ' := fun x ↦ if false = true then (w x)⁻¹ else w x)
        (by simp only [↓reduceIte]; exact hw.inv)
        (by simpa using hw) (by simpa using fun x ↦ inv_pos.2 (hwpos x)) (by simpa using hwpos)
        (fun x ↦ by simpa using inv_mul_cancel₀ (hwpos x).ne') u
      refine ⟨f, ?_, ?_⟩
      · filter_upwards [hf] with x hx
        rw [hx]
        simp only [↓reduceIte, Complex.ofReal_inv]
      · exact hpair
    obtain ⟨f, hf, hpair⟩ := key
    refine ⟨⟨f, (hiso f).2 fun k ↦ ?_⟩, ?_⟩
    · have hf' := (hqmp k).ae_eq_comp hf
      filter_upwards [hf', hu k, hf] with g h1 h2 h3
      simp only [comp_apply] at h1
      rw [h1, h2, h3, hwk, star_mul']
      simp only [hωinv, star_star]
      ring
    · change ∫ g, f g * u g ∂μ𝔽 ≠ 0
      simp_rw [mul_comm (f _)]
      rw [hpair]
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 hu0)

variable (F) in
/-- Paper: (10.2.1.3), p. 440, and (10.2.2.3), p. 445. Pull a functional
back along the quotient map and realize it in the reciprocal-weight Sobolev space. -/
def spectralSobolevDualEmbedding (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :
    StrongDual ℂ (spectralSobolevQuotient F a hI hs) →ₗ[ℂ] W'(l, r, s) :=
  (T(l, r, s, hI, hs)).toLinearEquiv.toLinearMap.comp
    ((Θ(a, hI, hs)).mkQL.precomp ℂ).toLinearMap

/-- A Hilbert quotient dual maps isometrically to the annihilator under an ambient duality. -/
private theorem spectralSobolevDualEmbedding_isometry_range_hilbert
    {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (N : Submodule ℂ E) [IsClosed (N : Set E)]
    (T : StrongDual ℂ E ≃ₗᵢ[ℂ] V) (B : E → V → ℂ)
    (hB : ∀ (Λ : StrongDual ℂ E) (x : E), Λ x = B x (T Λ)) :
    Isometry (fun Λ : StrongDual ℂ (E ⧸ N) ↦ T (Λ.comp N.mkQL)) ∧
      Set.range (fun Λ : StrongDual ℂ (E ⧸ N) ↦ T (Λ.comp N.mkQL)) =
        {v : V | ∀ x ∈ N, B x v = 0} := by
  let P : StrongDual ℂ (E ⧸ N) →ₗ[ℂ] StrongDual ℂ E :=
    (N.mkQL.precomp ℂ).toLinearMap
  have hnorm (Λ : StrongDual ℂ (E ⧸ N)) : ‖P Λ‖ = ‖Λ‖ := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Λ)
      intro x
      exact (Λ.le_opNorm (N.mkQL x)).trans
        (mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le N x) (norm_nonneg Λ))
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (P Λ))
      intro q
      let v : Nᗮ := N.quotientEquivOrthogonal q
      have hv : N.mkQL v.val = q := by
        change (Submodule.Quotient.mk v.val : E ⧸ N) = q
        exact (N.quotientEquivOrthogonal_symm_eq_mk v.val v.property).symm.trans
          (N.quotientEquivOrthogonal.symm_apply_apply q)
      have hn : ‖v.val‖ = ‖q‖ := N.quotientEquivOrthogonal.norm_map q
      calc
        ‖Λ q‖ = ‖(P Λ) v.val‖ := by
          change ‖Λ q‖ = ‖Λ (N.mkQL v.val)‖
          rw [hv]
        _ ≤ ‖P Λ‖ * ‖v.val‖ := (P Λ).le_opNorm v.val
        _ = ‖P Λ‖ * ‖q‖ := by rw [hn]
  have hP : Isometry P := AddMonoidHomClass.isometry_of_norm P hnorm
  refine ⟨T.isometry.comp hP, ?_⟩
  ext v
  constructor
  · rintro ⟨Λ, rfl⟩ x hx
    rw [← hB (Λ.comp N.mkQL) x]
    change Λ (Submodule.Quotient.mk x) = 0
    rw [(Submodule.Quotient.mk_eq_zero N).mpr hx, map_zero]
  · intro hv
    let φ : StrongDual ℂ E := T.symm v
    have hφ : N ≤ φ.ker := by
      intro x hx
      change φ x = 0
      rw [hB φ x]
      change B x (T (T.symm v)) = 0
      rw [T.apply_symm_apply]
      exact hv x hx
    refine ⟨N.liftQL φ hφ, ?_⟩
    have hcomp : (N.liftQL φ hφ).comp N.mkQL = φ := by
      ext x
      rfl
    change T ((N.liftQL φ hφ).comp N.mkQL) = v
    rw [hcomp]
    exact T.apply_symm_apply v

/-- Paper: (10.2.1.3), p. 440, and (10.2.2.3), p. 445. Pullback along the
quotient identifies its strong dual isometrically with the theta annihilator. -/
theorem spectralSobolevDualEmbedding_isometry_range (a : ℝ) {l r s : ℝ} (hI : l ≤ r)
    (hs : 0 ≤ s) :
    let D := spectralSobolevDualEmbedding F a hI hs
    Isometry D ∧ range D = {u | ∀ f ∈ Θ(a, hI, hs), pair(f, u) = 0} := by
  exact spectralSobolevDualEmbedding_isometry_range_hilbert
    (E := W(l, r, s)) (V := W'(l, r, s))
    (Θ(a, hI, hs)) (T(l, r, s, hI, hs))
    (spectralSobolevPairing (F := F))
    (fun Λ f ↦ (spectralSobolevPairing_dual hI hs Λ f).2)

end Quotients

/-- Paper: Notation 10.2.1.1, p. 440, and Notation 10.2.2.1, p. 445.
Choose one continuous unitary extension for each norm-one character. -/
def IsSpectralBasepointChoice (χ : PontryaginDual C₁ → PontryaginDual C𝔽) : Prop :=
  ∀ ω, (χ ω).comp restriction = ω

/-- Paper: Notation 10.2.1.1, p. 440. A splitting of the idele class norm
provides unitary lifts for all the norm-one characters at once. -/
theorem exists_spectralBasepointChoice (F : Type*) [Field F] [NumberField F] :
    ∃ χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F),
      IsSpectralBasepointChoice χ := by
  let C := IdeleClassGroup (𝓞 F) F
  let n : C →ₜ* ℝ≥0ˣ := continuousIdeleClassNorm F
  let q : IdeleGroup (𝓞 F) F →ₜ* C := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ : ℝ≥0ˣ →ₜ* C := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hσ : Function.RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let P : C →ₜ* C := ContinuousMonoidHom.id C / σ.comp n
  have hP (x : C) : P x ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (x / σ (ideleClassNorm F x)) = 1
    rw [map_div, hσ, div_self']
  let r : C →ₜ* (ideleClassNorm F).ker := ⟨P.toMonoidHom.codRestrict _ hP, P.continuous.subtype_mk _⟩
  refine ⟨fun ω ↦ ω.comp r, fun ω ↦ ?_⟩
  ext x : 1
  change ω (r (x : C)) = ω x
  apply congrArg ω
  apply Subtype.ext
  change (x : C) / σ (ideleClassNorm F x) = x
  rw [show ideleClassNorm F (x : C) = 1 from x.property, map_one, div_one]

/-- Paper: (10.2.1.4), p. 440. In each component the norm twists of the
chosen extension give its unique complex parameter. -/
theorem IsSpectralBasepointChoice.existsUnique_normTwist
    {χ : PontryaginDual C₁ → PontryaginDual C𝔽} (_hχ : IsSpectralBasepointChoice χ)
    (ω : PontryaginDual C₁) (c : QuasiCharacter C𝔽)
    (_hc : ∀ g : C₁, c g.val = (ω g : ℂ)) :
    ∃! z : ℂ, c = ideleClassNormTwist (χ ω) z := by
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hσ : Function.RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  let d := c * j.comp (χ ω)⁻¹
  have hd (g : C𝔽) : d g = c g / (χ ω g : ℂ) := by
    change c g * (((χ ω g)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv, div_eq_mul_inv]
  have hk (g : C₁) : d g = 1 := by
    have hres : χ ω (g : C𝔽) = ω g := DFunLike.congr_fun (_hχ ω) g
    rw [hd, _hc g, hres, div_self (Circle.coe_ne_zero _)]
  obtain ⟨z, hz, huniq⟩ := existsUnique_complexPower (d.comp σ)
  refine ⟨z, ?_, fun w hw ↦ ?_⟩
  · ext g : 1
    let t := ideleClassNorm F g
    have hg : g / σ t ∈ (ideleClassNorm F).ker := by
      change ideleClassNorm F (g / σ t) = 1
      rw [map_div, hσ t, div_self']
    have hr : d g = (((t : ℝ≥0) : ℝ) : ℂ) ^ z := calc
      d g = d (g / σ t) * d (σ t) := by rw [← map_mul, div_mul_cancel]
      _ = _ := by rw [hk ⟨_, hg⟩, one_mul]; exact hz t
    change c g = (χ ω g : ℂ) * _
    exact ((div_eq_iff (Circle.coe_ne_zero _)).mp ((hd g).symm.trans hr)).trans (mul_comm _ _)
  · apply huniq
    intro t
    change d (σ t) = _
    rw [hd, hw]
    change ((χ ω (σ t) : ℂ) * (((ideleClassNorm F (σ t)).val : ℝ) : ℂ) ^ w) / _ = _
    rw [hσ t, mul_div_cancel_left₀ _ (Circle.coe_ne_zero _)]

local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "vanishingOrder(" χ ", " z ")" =>
  meromorphicOrderAt (continuedCompletedHeckeL χ) z

/-- Paper: (10.2.1.5), p. 440, and (10.2.2.4), p. 446. A zero jet is the
chosen base character times the norm twist and a power of the log norm.
The line jet has real offset zero. -/
def spectralZeroJet (χ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (g : C𝔽) : ℂ :=
  ideleClassNormTwist χ (shift(b, t)) g * (logNorm g : ℂ) ^ k

/-- Paper: (10.2.1.5), p. 440, and (10.2.2.4), p. 446. The zeroth jet at
twist zero is the base character.
Deviation: Sanity check in degree and twist zero. -/
theorem spectralZeroJet_zero (χ : PontryaginDual C𝔽) (g : C𝔽) :
    spectralZeroJet χ 0 0 0 g = (χ g : ℂ) := by
  unfold spectralZeroJet
  simp only [pow_zero, mul_one, Complex.ofReal_zero, zero_mul, add_zero]
  change (χ g : ℂ) * _ ^ (0 : ℂ) = _
  rw [Complex.cpow_zero, mul_one]

/-- Paper: (10.2.1.6), p. 440, and (10.2.2.5), p. 446. Truncate the
multiplicity to the number of integrable jet orders at the boundary.
Deviation: Use the ceiling of (s−1)/2. The floor of (s−1)/2+1 admits the
logarithmically divergent endpoint when (s−1)/2 is an integer. -/
def spectralBoundaryMultiplicity (s : ℝ) (N : ℕ) : ℕ :=
  min N (Nat.ceil ((s - 1) / 2))

/-- Paper: (10.2.1.6), p. 440, and (10.2.2.5), p. 446. An order survives
the boundary cutoff exactly when it is below the zero multiplicity and strictly
below the reciprocal-weight integrability threshold.
Deviation: The limiting jet is excluded. -/
theorem lt_spectralBoundaryMultiplicity (s : ℝ) (N k : ℕ) :
    k < spectralBoundaryMultiplicity s N ↔ k < N ∧ (k : ℝ) < (s - 1) / 2 := by
  rw [spectralBoundaryMultiplicity, lt_min_iff, Nat.lt_ceil]

/-- Paper: Remark 10.2.1.2, pp. 440–441. A Markushevich system in the paper's
Hilbert setting is biorthogonal and both linear spans are norm dense.
Deviation: An arbitrary index type permits a finite or empty enumeration. -/
def IsSpectralMarkushevichBasis {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : ι → E) (Λ : ι → StrongDual ℂ E) : Prop :=
  (∀ i, Λ i (x i) = 1) ∧ (∀ i j, i ≠ j → Λ j (x i) = 0) ∧
    Dense (Submodule.span ℂ (range x) : Set E) ∧
    Dense (Submodule.span ℂ (range Λ) : Set (StrongDual ℂ E))

/-- Paper: Remark 10.2.1.2, p. 440. The dense functional family determines
its biorthogonal vectors uniquely. -/
theorem IsSpectralMarkushevichBasis.unique_vectors {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {x y : ι → E} {Λ : ι → StrongDual ℂ E}
    (_hx : IsSpectralMarkushevichBasis x Λ) (_hy : IsSpectralMarkushevichBasis y Λ) :
    x = y := by
  funext i
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  have he : ContinuousLinearMap.apply ℂ ℂ (x i) = ContinuousLinearMap.apply ℂ ℂ (y i) := by
    apply ContinuousLinearMap.ext_on _hx.2.2.2
    rintro _ ⟨j, rfl⟩
    change Λ j (x i) = Λ j (y i)
    by_cases hij : i = j
    · subst j
      exact (_hx.1 i).trans (_hy.1 i).symm
    · exact (_hx.2.1 i j hij).trans (_hy.2.1 i j hij).symm
  exact fun ℓ ↦ DFunLike.congr_fun he ℓ

local notation "multiplicity(" χ ", " z ")" => (vanishingOrder(χ, z)).untop₀.toNat

/-- Paper: Theorem 10.2.1.1, p. 440. Index the a-line jets by norm-one
characters, zero ordinates, and surviving derivative orders. Meromorphic order
excludes poles, even when the continuation has been assigned a value there.
Deviation: Apply the strict integrability cutoff of (10.2.1.6). -/
abbrev SpectralLineJetIndex (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a s : ℝ) :=
  {j : PontryaginDual C₁ × ℝ × ℕ //
    j.2.2 < spectralBoundaryMultiplicity s (multiplicity(χ j.1, shift(a, j.2.1)))}

/-- Paper: Theorem 10.2.1.1, p. 440. Every admitted a-line jet has positive
derivative capacity, so its indexing point is a zero of the completed L-function. -/
theorem SpectralLineJetIndex.order_pos {χ : PontryaginDual C₁ → PontryaginDual C𝔽} {a s : ℝ}
    (j : SpectralLineJetIndex χ a s) : 0 < vanishingOrder(χ j.val.1, shift(a, j.val.2.1)) := by
  have key : ∀ o : WithTop ℤ, 0 < o.untop₀.toNat → 0 < o := by
    intro o h
    cases o with
    | top => simp at h
    | coe n =>
      rw [WithTop.untop₀_coe] at h
      exact_mod_cast (by omega : 0 < n)
  have h := j.2
  unfold spectralBoundaryMultiplicity at h
  exact key _ (by omega)

local notation "lineJet(" χ ", " j ")" => spectralZeroJet (χ (j).val.1) 0 (j).val.2.1 (j).val.2.2
local notation "stripJet(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "L2μ'(" l ", " r ", " s ")" => (μ𝔽 |>.withDensity fun g ↦
  ENNReal.ofReal (intervalSobolevDensity l r s (logNorm g))⁻¹)

-- On p. 443 an outside-band evaluation vanishes on the band image. Its
-- dual inner product with an inside-band evaluation can be nonzero:
-- for s = 2 on the rational trivial component the Gram kernel is
-- proportional to exp(-|t-u|). The claimed orthogonal adjoint range fails.

/-- A logarithmic power below the strict cutoff is square-integrable for the reciprocal weight. -/
private theorem spectralLineJet_memLp_of_norm_sq
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (μ : Measure G) [μ.IsHaarMeasure] (s : ℝ) (k : ℕ)
    (hk : 2 * (k : ℝ) + 1 < s) (u : G → ℂ) (hu : Continuous u)
    (hnorm : ∀ g : G, ‖u g‖ ^ 2 = (Real.log ((m g).val : ℝ)) ^ (2 * k)) :
    MemLp u 2 (μ.withDensity fun g ↦
      ENNReal.ofReal (((1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2))⁻¹)) := by
  let ν : Measure G := canonicalModulatedHaar m hm
  let : ν.IsHaarMeasure :=
    (existsUnique_canonicalModulatedHaar m hm).exists.choose_spec.1
  have hν : Integrable (fun g : G ↦ (Real.log ((m g).val : ℝ)) ^ (2 * k) *
      ((1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2))⁻¹) ν :=
    (sobolev_log_preserving m hm hms).integrable_comp_of_integrable
      (integrable_pow_mul_rpow_inv hk)
  have hμ : Integrable (fun g : G ↦ (Real.log ((m g).val : ℝ)) ^ (2 * k) *
      ((1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2))⁻¹) μ := by
    rw [Measure.isMulLeftInvariant_eq_smul μ ν]
    exact hν.smul_measure_nnreal
  have hρpos (g : G) : 0 < (1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hρ : Continuous (fun g : G ↦ (1 + (Real.log ((m g).val : ℝ)) ^ 2) ^ (s / 2)) :=
    ((continuous_const : Continuous (fun _ : G ↦ (1 : ℝ))).add
      ((continuous_logModule' m).pow 2)).rpow_const (fun g ↦ Or.inl (by
        change (1 : ℝ) + (Real.log ((m g).val : ℝ)) ^ 2 ≠ 0
        positivity))
  apply (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).2
  apply (integrable_withDensity_iff
    (hρ.inv₀ (fun g ↦ (hρpos g).ne')).measurable.ennreal_ofReal
    (ae_of_all μ fun _ ↦ ENNReal.ofReal_lt_top)).2
  refine hμ.congr (ae_of_all μ fun g ↦ ?_)
  dsimp only [Pi.inv_apply]
  rw [hnorm g, ENNReal.toReal_ofReal (inv_nonneg.mpr (hρpos g).le)]

/-- Paper: Theorem 10.2.1.1, p. 440. The admitted a-line jets are elements of
the reciprocal-weight Hilbert space.
Deviation: Exclude the divergent endpoint of (10.2.1.6). -/
theorem spectralLineJet_memLp (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ}
    (_hs : 1 < s) (j : SpectralLineJetIndex χ a s) :
    MemLp (lineJet(χ, j)) 2 (L2μ'(0, 0, s)) := by
  have horder : (j.val.2.2 : ℝ) < (s - 1) / 2 :=
    ((lt_spectralBoundaryMultiplicity s _ _).mp j.property).2
  have hk : 2 * (j.val.2.2 : ℝ) + 1 < s := by linarith
  let u : C𝔽 → ℂ := spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
  have hu : Continuous u :=
    (ideleClassNormTwist (χ j.val.1)
      ((0 : ℂ) + (j.val.2.1 : ℂ) * Complex.I)).continuous.mul
      ((Complex.continuous_ofReal.comp (continuous_logModule' m𝔽)).pow j.val.2.2)
  have hnorm (g : C𝔽) : ‖u g‖ ^ 2 = (logNorm g) ^ (2 * j.val.2.2) := by
    have htwist : ‖ideleClassNormTwist (χ j.val.1)
        ((0 : ℂ) + (j.val.2.1 : ℂ) * Complex.I) g‖ = 1 := by
      change ‖(χ j.val.1 g : ℂ) *
        (((ideleClassNorm F g).val : ℝ) : ℂ) ^
          ((0 : ℂ) + (j.val.2.1 : ℂ) * Complex.I)‖ = 1
      rw [norm_mul, Circle.norm_coe, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos
          (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g)))]
      simp
    change ‖ideleClassNormTwist (χ j.val.1)
      ((0 : ℂ) + (j.val.2.1 : ℂ) * Complex.I) g *
        (logNorm g : ℂ) ^ j.val.2.2‖ ^ 2 = _
    rw [norm_mul, htwist, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc
      (|logNorm g| ^ j.val.2.2) ^ 2 =
          (|logNorm g| ^ 2) ^ j.val.2.2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm j.val.2.2 2]
      _ = ((logNorm g) ^ 2) ^ j.val.2.2 :=
        congrArg (fun y : ℝ ↦ y ^ j.val.2.2) (sq_abs (logNorm g))
      _ = (logNorm g) ^ (2 * j.val.2.2) := (pow_mul _ _ _).symm
  have h := spectralLineJet_memLp_of_norm_sq m𝔽 hm𝔽 hms𝔽 μ𝔽 s j.val.2.2 hk u hu hnorm
  change MemLp u 2 ((μ𝔽).withDensity fun g ↦
    ENNReal.ofReal (((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹)) at h
  simpa only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero,
    max_self, one_mul, u] using h

-- For a family of admitted jets u, these are the two analytic inputs to
-- the Hilbert-space argument. Interpolants are lifted to the ambient space.
local notation "JetKernel(" a ", " hI ", " hs ", " u ")" =>
  (∀ f, f ∈ Θ(a, hI, hs) ↔ ∀ j, spectralSobolevPairing (F := F) f (u j) = 0)
local notation "JetInterpolation(" J ", " a ", " hI ", " hs ", " u ")" =>
  (∃ v : J → W(_, _, _), (∀ i, spectralSobolevPairing (F := F) (v i) (u i) = 1) ∧
    (∀ i j, i ≠ j → spectralSobolevPairing (F := F) (v i) (u j) = 0) ∧
    Dense (Submodule.span ℂ (range (fun i ↦ (Θ(a, hI, hs)).mkQ (v i))) :
      Set (spectralSobolevQuotient F a hI hs)))

/-- A total family of continuous functionals on a Hilbert space has norm-dense span. -/
private theorem spectralSobolevQuotient_basis_of_interpolation_dense_dual
    {Q J : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (Λ : J → StrongDual ℂ Q)
    (h : ∀ q : Q, (∀ j, Λ j q = 0) → q = 0) :
    Dense (Submodule.span ℂ (Set.range Λ) : Set (StrongDual ℂ Q)) := by
  let R := InnerProductSpace.toDual ℂ Q
  let v : J → Q := fun j ↦ R.symm (Λ j)
  have hv : Dense (Submodule.span ℂ (Set.range v) : Set Q) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro q hq
    apply h q
    intro j
    have hz := (Submodule.mem_orthogonal (Submodule.span ℂ (Set.range v)) q).mp hq
      (v j) (Submodule.subset_span (Set.mem_range_self j))
    simpa only [v, R, InnerProductSpace.toDual_symm_apply] using hz
  apply (R.surjective.denseRange.dense_image R.continuous hv).mono
  apply (Submodule.image_span_subset R.toLinearEquiv.toLinearMap
    (Set.range v) (Submodule.span ℂ (Set.range Λ))).mpr
  rintro _ ⟨j, rfl⟩
  change R (R.symm (Λ j)) ∈ Submodule.span ℂ (Set.range Λ)
  rw [R.apply_symm_apply]
  exact Submodule.subset_span (Set.mem_range_self j)

/-- Dense interpolants and a total lifted dual family form a spectral Markushevich basis. -/
private theorem spectralSobolevQuotient_basis_of_interpolation_construct
    {J E Q U : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (q : E → Q) (hq : Function.Surjective q)
    (D : StrongDual ℂ Q → U) (b : E → U → ℂ) (u : J → U)
    (hpair : ∀ (Λ : StrongDual ℂ Q) (f : E), Λ (q f) = b f (D Λ))
    (hu : ∀ j, ∃ Λ : StrongDual ℂ Q, D Λ = u j)
    (hzero : ∀ f : E, (∀ j, b f (u j) = 0) → q f = 0)
    (hV : ∃ v : J → E,
      (∀ i, b (v i) (u i) = 1) ∧
      (∀ i j, i ≠ j → b (v i) (u j) = 0) ∧
      Dense (Submodule.span ℂ (Set.range (fun i ↦ q (v i))) : Set Q)) :
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j, D (Λ j) = u j := by
  classical
  choose Λ hΛ using hu
  obtain ⟨v, hvself, hvcross, hvdense⟩ := hV
  have he (j : J) (f : E) : Λ j (q f) = b f (u j) :=
    (hpair (Λ j) f).trans (congrArg (b f) (hΛ j))
  refine ⟨fun j ↦ q (v j), Λ, ?_, hΛ⟩
  refine ⟨fun i ↦ (he i (v i)).trans (hvself i),
    fun i j hij ↦ (he j (v i)).trans (hvcross i j hij), hvdense, ?_⟩
  apply spectralSobolevQuotient_basis_of_interpolation_dense_dual Λ
  intro z hz
  obtain ⟨f, rfl⟩ := hq z
  apply hzero f
  intro j
  exact (he j f).symm.trans (hz j)

/-- Paper: Theorems 10.2.1.1 and 10.2.2.1, pp. 440, 446. A common kernel
identifies the closed dual span in the Hilbert quotient. A dense family of
interpolants then supplies the other half of the Markushevich basis. -/
theorem spectralSobolevQuotient_basis_of_interpolation {J : Type*}
    (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) (u : J → W'(l, r, s))
    (_hK : JetKernel(a, hI, hs, u)) (_hV : JetInterpolation(J, a, hI, hs, u)) :
    let Q := spectralSobolevQuotient F a hI hs
    let D := spectralSobolevDualEmbedding F a hI hs
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j, D (Λ j) = u j := by
  classical
  let N := globalThetaSobolev F a hI hs
  let D := spectralSobolevDualEmbedding F a hI hs
  have hpair (Λ : StrongDual ℂ (spectralSobolevQuotient F a hI hs))
      (f : W(l, r, s)) :
      Λ (N.mkQ f) = spectralSobolevPairing f (D Λ) := by
    exact (spectralSobolevPairing_dual hI hs (Λ.comp N.mkQL) f).2
  have hu (j : J) :
      ∃ Λ : StrongDual ℂ (spectralSobolevQuotient F a hI hs), D Λ = u j := by
    have hj : u j ∈ Set.range (spectralSobolevDualEmbedding F a hI hs) := by
      rw [(spectralSobolevDualEmbedding_isometry_range (F := F) a hI hs).2]
      exact fun f hf ↦ (_hK f).mp hf j
    exact hj
  refine spectralSobolevQuotient_basis_of_interpolation_construct
    (Q := spectralSobolevQuotient F a hI hs)
    N.mkQ N.mkQ_surjective D (spectralSobolevPairing (F := F)) u hpair hu ?_ _hV
  intro f hf
  exact (spectralSobolevQuotient_eq_zero a hI hs f).mpr ((_hK f).mpr hf)

local notation "lineHs(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "lineU(" χ ", " hs ")" =>
  (fun j ↦ (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j)))

/-- Paper: Theorem 10.2.1.1, p. 440. The norm-one dual and the discrete
zero sets in its charts give countably many admitted line jets. -/
theorem spectralLineJet_countable (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a s : ℝ) :
    Countable (SpectralLineJetIndex χ a s) := by
  have hK : IsCompact ((ideleClassNorm F).ker : Set C𝔽) :=
    IsModulation.isCompact_ker (m := m𝔽) hm𝔽
  let : CompactSpace C₁ := isCompact_iff_compactSpace.mp hK
  let : LocallyCompactSpace C₁ := hK.isClosed.locallyCompactSpace
  let : SecondCountableTopology C₁ := Topology.IsInducing.subtypeVal.secondCountableTopology
  let : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual C₁) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap C₁ Circle).secondCountableTopology
  let : Countable (PontryaginDual C₁) := countable_of_Lindelof_of_discrete
  let Z (ω : PontryaginDual C₁) := {z : ℂ | 0 < multiplicity(χ ω, z)}
  have hc (ω : PontryaginDual C₁) : (Z ω).Countable := by
    have hm := (continuedCompletedHeckeL_spec (χ ω)).1.meromorphicOn
    have hcod : (Z ω)ᶜ ∈ Filter.codiscrete ℂ := by
      filter_upwards [hm.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top] with z hz
      rcases hz.2 with h | h <;> simp [Z, h]
    let : DiscreteTopology (Z ω) := isDiscrete_iff_discreteTopology.mp
      (compl_mem_codiscrete_iff.mp hcod).2
    exact Set.countable_coe_iff.mp countable_of_Lindelof_of_discrete
  let W := ⋃ ω, Z ω
  let : Countable W := (Set.countable_iUnion hc).to_subtype
  have hz (j : SpectralLineJetIndex χ a s) : shift(a, j.val.2.1) ∈ W := by
    apply Set.mem_iUnion.mpr
    refine ⟨j.val.1, ?_⟩
    exact Nat.zero_lt_of_lt (lt_of_lt_of_le j.property (min_le_left _ _))
  let e (j : SpectralLineJetIndex χ a s) : PontryaginDual C₁ × W × ℕ :=
    (j.val.1, ⟨shift(a, j.val.2.1), hz j⟩, j.val.2.2)
  apply Function.Injective.countable (f := e)
  intro i j hij
  have him := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.1.val.im) hij
  have hω := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.1) hij
  have hk := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.2) hij
  exact Subtype.ext (Prod.ext hω (Prod.ext (by simpa [e] using him) hk))

section TestDuality

local notation "E" => ModulatedExponentialDecay m𝔽 univ
local notation "ρE" => (exists_modulatedExponentialDecay_translationAction m𝔽 univ
  hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose
local notation "Eω(" ω ")" => actionIsotype ((ρE).comp (ideleClassNorm F).ker.subtype) ω
local notation "ℬ₀" => ↥(adelePolarSubspace F)

/-- A jointly continuous family on a compact parameter space preserves sequence
convergence uniformly in the parameter. -/
private theorem existsUnique_spectralLineTestCompletion_uniform
    {H Z : Type*} [TopologicalSpace H] [CompactSpace H] [UniformSpace Z]
    (T : H → Z → Z) (hT : Continuous (fun p : H × Z ↦ T p.1 p.2))
    (u : ℕ → Z) (v : Z) (hu : Tendsto u atTop (𝓝 v)) :
    TendstoUniformly (fun n k ↦ T k (u n)) (fun k ↦ T k v) atTop := by
  intro U hU
  have hc : Continuous (fun p : Z × H ↦ T p.2 p.1) := hT.comp continuous_swap
  obtain ⟨V, hV, h⟩ := (isCompact_univ (X := H)).mem_uniformity_of_prod
    (f := fun f : Z ↦ fun k : H ↦ T k f)
    (s := univ) (q := v) hc.continuousOn (mem_univ v) (symm_le_uniformity hU)
  rw [nhdsWithin_univ] at hV
  filter_upwards [hu.eventually hV] with n hn k
  exact h (u n) hn k (mem_univ k)

/-- Compact character averaging preserves density of an equivariant map. -/
private theorem existsUnique_spectralLineTestCompletion_dense
    {H X Y : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [MeasurableSpace H] [BorelSpace H] [CompactSpace H]
    [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
    [T2Space X] [PolynormableSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (μ : Measure H) [μ.IsHaarMeasure]
    (σ : H →* (X →L[ℂ] X)) (τ : H →* (Y →L[ℂ] Y))
    (hσ : Continuous (fun p : H × X ↦ σ p.1 p.2))
    (hτ : Continuous (fun p : H × Y ↦ τ p.1 p.2))
    (hborn : ∀ p : Seminorm ℂ X,
      (∀ B : Set X, Bornology.IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p)
    (ω : PontryaginDual H) (j : X →L[ℂ] Y) (hd : DenseRange j)
    (heq : ∀ k f, j (σ k f) = τ k (j f))
    (i : actionIsotype σ ω →L[ℂ] actionIsotype τ ω)
    (hi : ∀ f, (i f : Y) = j (f : X)) : DenseRange i := by
  letI : Module ℝ X := Module.restrictScalars ℝ ℂ X
  letI : IsScalarTower ℝ ℂ X := IsScalarTower.restrictScalars ℝ ℂ X
  letI : LocallyConvexSpace ℝ X :=
    (PolynormableSpace.withSeminorms ℂ X).toLocallyConvexSpace
  letI : NormedSpace ℝ Y := NormedSpace.complexToReal
  have hbornY (p : Seminorm ℂ Y)
      (hp : ∀ B : Set Y, Bornology.IsVonNBounded ℂ B → BddAbove (p '' B)) :
      Continuous p := by
    obtain ⟨M, hM⟩ := hp _ (NormedSpace.isVonNBounded_closedBall ℂ Y 1)
    have hball : p.closedBall 0 (max M 0 + 1) ∈ 𝓝 (0 : Y) := by
      refine Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : Y) zero_lt_one) ?_
      intro x hx
      rw [Seminorm.mem_closedBall_zero]
      exact (hM ⟨x, hx, rfl⟩).trans
        (le_of_lt <| lt_of_le_of_lt (le_max_left M 0) (lt_add_one _))
    exact p.continuous' hball
  obtain ⟨A, hA⟩ := (existsUnique_compactActionIsotypicAverage μ σ hσ
    hborn (existsUnique_spectralLineTestCompletion_uniform (Z := X)
      (fun k f ↦ σ k f) hσ) ω).exists
  obtain ⟨B, hB⟩ := (existsUnique_compactActionIsotypicAverage μ τ hτ
    hbornY (existsUnique_spectralLineTestCompletion_uniform (Z := Y)
      (fun k f ↦ τ k f) hτ) ω).exists
  have hrangeA := compactActionAverage_range μ σ hσ ω A hA
  have hrangeB := compactActionAverage_range μ τ hτ ω B hB
  let A' := A.codRestrict (actionIsotype σ ω) (by
    intro u
    rw [← hrangeA]
    exact ⟨u, rfl⟩)
  let B' := B.codRestrict (actionIsotype τ ω) (by
    intro u
    rw [← hrangeB]
    exact ⟨u, rfl⟩)
  have hsurj : Surjective B' := by
    intro u
    have hu : (u : Y) ∈ B.toLinearMap.range := hrangeB.symm ▸ u.property
    obtain ⟨v, hv⟩ := hu
    exact ⟨v, Subtype.ext hv⟩
  have hcomm (f : X) : j (A f) = B (j f) := by
    letI : SeparatingDual ℂ Y := locallyConvexSpace_separatingDual ℂ Y
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro φ
    obtain ⟨_, hs⟩ := hA f
    obtain ⟨_, ht⟩ := hB (j f)
    have hs' := LinearMap.congr_fun hs (φ.comp j)
    have ht' := LinearMap.congr_fun ht φ
    change φ (j (A f)) =
      ∫ k : H, φ (j (star (ω k : ℂ) • σ k f)) ∂μ.restrict univ at hs'
    change φ (B (j f)) =
      ∫ k : H, φ (star (ω k : ℂ) • τ k (j f)) ∂μ.restrict univ at ht'
    simpa only [map_smul j, heq, ← ht'] using hs'
  have hcomp : (i : _ → _) ∘ A' = (B' : _ → _) ∘ j :=
    funext fun f ↦ Subtype.ext ((hi (A' f)).trans (hcomm f))
  apply DenseRange.of_comp (g := A')
  rw [hcomp]
  exact hsurj.denseRange.comp hd B'.continuous

/-- Paper: (10.2.1.7), p. 441. The weighted completion map on exponential-decay
tests preserves the norm-one isotype and has dense image in its Sobolev isotype.
Its transpose evaluates by pairing with the weighted test.
Deviation: The transpose uses the conjugate isotype in the negative space.
The norm weight is applied to the full test space in the diagram. Appendix D's
two-sided decay topology uses growing exponential weights in log coordinates.
The decaying factors on p. 441 would all be bounded by the zeroth weight. -/
theorem existsUnique_spectralLineTestCompletion (a : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    ∃! i : Eω(ω) →L[ℂ] Wω(le_rfl (a := (0 : ℝ)), hs, ω),
      (∀ φ, ((i φ).val : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a φ.val.val) ∧
        DenseRange i ∧
        ∃ T : W'(0, 0, s) →L[ℂ] StrongDual ℂ Eω(ω),
          (∀ u φ, T u φ = spectralSobolevPairing (F := F) (i φ).val u) ∧
          ∀ u, (∀ k : C₁, (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽]
            fun g ↦ (ω⁻¹ k : ℂ) * u g) → T u = 0 → u = 0 := by
  have hshift : (fun b : ℝ ↦ b - a) '' univ = univ :=
    image_univ_of_surjective fun b ↦ ⟨b + a, add_sub_cancel_right b a⟩
  have hShiftEx : ∃ S : E ≃L[ℂ] E,
      ∀ f, (S f).val = modulationWeight m𝔽 a f.val :=
    (congrArg (fun J : Set ℝ ↦ ∃ S : E ≃L[ℂ] ModulatedExponentialDecay m𝔽 J,
      ∀ f, (S f).val = modulationWeight m𝔽 a f.val) hshift).mp
      (modulatedExponentialDecay_shift_equiv (G := C𝔽) m𝔽 univ hm𝔽 hms𝔽
        ordConnected_univ univ_nonempty a)
  let S := hShiftEx.choose
  have hS := hShiftEx.choose_spec
  have hDenseEx :=
    modulatedIntervalSobolev_dense (G := C𝔽) m𝔽 hm𝔽 0 0 s le_rfl hs univ
      isOpen_univ ordConnected_univ (subset_univ _)
  let j₀ := hDenseEx.choose
  have hj₀inj := hDenseEx.choose_spec.1
  have hj₀dense := hDenseEx.choose_spec.2.1
  have hj₀coe := hDenseEx.choose_spec.2.2
  have hEquivEx := globalThetaAmbient_equiv_canonical (F := F) hm𝔽 0 0 s
  let e := hEquivEx.choose
  have he := hEquivEx.choose_spec
  let j : E →L[ℂ] W(0, 0, s) :=
    e.symm.toContinuousLinearMap.comp (j₀.comp S.toContinuousLinearMap)
  have hjinj : Injective j := e.symm.injective.comp (hj₀inj.comp S.injective)
  have hjdense : DenseRange j := e.symm.surjective.denseRange.comp
    (hj₀dense.comp S.surjective.denseRange j₀.continuous) e.symm.continuous
  have hj (f : E) : (j f : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a f.val := by
    have h₀ : (j₀ (S f) : C𝔽 → ℂ) =ᵐ[μ𝔽] (S f).val := by
      rw [ideleClassTamagawaMeasure_eq_smul_canonical (F := F)]
      exact Measure.ae_smul_measure (hj₀coe (S f)) _
    have he' := (he (j f)).1
    have hej : e (j f) = j₀ (S f) := by simp [j]
    rw [hej] at he'
    exact he'.symm.trans (h₀.trans (ae_of_all _ fun g ↦ congrFun (hS f) g))
  let σ : C₁ →* (E →L[ℂ] E) := (ρE).comp (ideleClassNorm F).ker.subtype
  let τ : C₁ →* (W(0, 0, s) →L[ℂ] W(0, 0, s)) := ρ(0, 0, s, le_rfl, hs)
  have hE := (exists_modulatedExponentialDecay_translationAction (G := C𝔽) m𝔽 univ
    hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose_spec
  have hjρ (k : C₁) (f : E) : j (σ k f) = τ k (j f) := by
    apply Lp.ext
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
    have htr := hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s le_rfl hs k.val (j f)
    have ht := (measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving.ae_eq_comp (hj f)
    filter_upwards [hj (σ k f), htr, ht] with g hleft hright hcomp
    change (j f) (k.val⁻¹ * g) = (modulationWeight m𝔽 a f.val) (k.val⁻¹ * g) at hcomp
    have hweight : (modulationWeight m𝔽 a (σ k f).val) g =
        (modulationWeight m𝔽 a f.val) (k.val⁻¹ * g) := by
      have hk : m𝔽 k.val = 1 := k.property
      have hn : m𝔽 (k.val⁻¹ * g) = m𝔽 g := by
        rw [map_mul, map_inv, hk, inv_one, one_mul]
      change Complex.ofReal (((m𝔽 g).val : ℝ) ^ a) * ((ρE) k.val f).val g =
        Complex.ofReal (((m𝔽 (k.val⁻¹ * g)).val : ℝ) ^ a) * f.val (k.val⁻¹ * g)
      have hv := congrArg (fun z : ℂ ↦ Complex.ofReal (((m𝔽 g).val : ℝ) ^ a) * z)
        (hE.1 k.val f g)
      have hw := congrArg (fun t : ℝ≥0ˣ ↦
        Complex.ofReal ((t.val : ℝ) ^ a) * f.val (k.val⁻¹ * g)) hn.symm
      exact hv.trans hw
    exact hleft.trans (hweight.trans (hcomp.symm.trans hright.symm))
  let i : actionIsotype σ ω →L[ℂ] actionIsotype τ ω :=
    (j.comp (actionIsotype σ ω).subtypeL).codRestrict (actionIsotype τ ω) (by
      intro φ
      apply (mem_actionIsotype τ ω _).2
      intro k
      change τ k (j φ.val) = (ω k : ℂ) • j φ.val
      rw [← hjρ, ((mem_actionIsotype σ ω _).1 φ.property k), map_smul])
  have hicoe (φ : Eω(ω)) : ((i φ).val : C𝔽 → ℂ) =ᵐ[μ𝔽]
      modulationWeight m𝔽 a φ.val.val := hj φ.val
  letI : T2Space E := T2Space.of_injective_continuous (f := j) hjinj j.continuous
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let sectionNorm : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hsection : Function.RightInverse sectionNorm m𝔽 := canonicalIdeleNormSection_rightInverse F
  letI : CompleteSpace E := modulatedExponentialDecay_complete (G := C𝔽) m𝔽 univ hm𝔽
    ordConnected_univ univ_nonempty sectionNorm hsection
  letI : CompactSpace C₁ :=
    isCompact_iff_compactSpace.mp (IsModulation.isCompact_ker (m := m𝔽) hm𝔽)
  letI : MeasurableSpace C₁ := borel _
  letI : BorelSpace C₁ := ⟨rfl⟩
  have hσ : Continuous (fun p : C₁ × E ↦ σ p.1 p.2) :=
    hE.2.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hτ : Continuous (fun p : C₁ × W(0, 0, s) ↦ τ p.1 p.2) :=
    (exists_hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).choose_spec.2.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hidense : DenseRange i := existsUnique_spectralLineTestCompletion_dense
    (H := C₁) (X := E) (Y := W(0, 0, s)) Measure.haar σ τ hσ hτ
    (modulatedExponentialDecay_bornological (G := C𝔽) m𝔽 univ hm𝔽 ordConnected_univ
      univ_nonempty sectionNorm hsection) ω j hjdense hjρ i (fun _ ↦ rfl)
  let D : StrongDual ℂ W(0, 0, s) ≃ₗᵢ[ℂ] W'(0, 0, s) :=
    (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 0 0 s le_rfl hs).exists.choose
  let T' : W'(0, 0, s) →L[ℂ] StrongDual ℂ Eω(ω) :=
    (((actionIsotype τ ω).subtypeL.comp i).precomp ℂ).comp
      D.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hT (u : W'(0, 0, s)) (φ : Eω(ω)) :
      T' u φ = spectralSobolevPairing (F := F) (i φ).val u := by
    change (D.symm u) (i φ).val = _
    have h := (spectralSobolevPairing_dual le_rfl hs (D.symm u) (i φ).val).2
    change (D.symm u) (i φ).val = spectralSobolevPairing (F := F) (i φ).val
      (D (D.symm u)) at h
    exact h.trans (congrArg (spectralSobolevPairing (F := F) (i φ).val) (D.apply_symm_apply u))
  refine ⟨i, ⟨hicoe, hidense, T', hT, ?_⟩, ?_⟩
  · intro u hu hTu
    let Λ : StrongDual ℂ (actionIsotype τ ω) := (D.symm u).comp (actionIsotype τ ω).subtypeL
    have hΛ : Λ = 0 := by
      apply DFunLike.coe_injective
      apply hidense.equalizer Λ.continuous (0 : StrongDual ℂ (actionIsotype τ ω)).continuous
      funext φ
      change T' u φ = 0
      exact congrArg (fun L : StrongDual ℂ Eω(ω) ↦ L φ) hTu
    by_contra hu0
    obtain ⟨f, hf⟩ := (spectralSobolevPairing_isotype le_rfl hs ω).2 u hu hu0
    apply hf
    have h := (spectralSobolevPairing_dual le_rfl hs (D.symm u) f.val).2
    change (D.symm u) f.val = spectralSobolevPairing (F := F) f.val
      (D (D.symm u)) at h
    exact (h.trans (congrArg (spectralSobolevPairing (F := F) f.val)
      (D.apply_symm_apply u))).symm.trans
        (congrArg (fun L : StrongDual ℂ (actionIsotype τ ω) ↦ L f) hΛ)
  · intro i' hi'
    apply ContinuousLinearMap.ext
    intro φ
    apply Subtype.ext
    exact Lp.ext ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq
      ((hi'.1 φ).trans (hicoe φ).symm))

/-- Paper: (10.2.1.8), pp. 441–442. Pullback sends a functional on the
isotypic Sobolev quotient injectively into the test dual and annihilates
the polar-free theta tests of that isotype.
Deviation: Pull back along the norm-weighted completion map of (10.2.1.7). -/
theorem spectralLineIsotypeDual_pullback (a : ℝ) {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    let hI : (0 : ℝ) ≤ 0 := le_rfl
    let N := (Θ(a, hI, hs)).comap (Wω(hI, hs, ω)).subtype
    let i := (existsUnique_spectralLineTestCompletion a hs ω).exists.choose
    let D : StrongDual ℂ (spectralSobolevIsotypeQuotient F a hI hs ω) →L[ℂ]
        StrongDual ℂ Eω(ω) := (N.mkQL.comp i).precomp ℂ
    Injective D ∧ ∀ Λ (φ : Eω(ω)) (f : ℬ₀), φ.val.val = homogeneousAdelicTheta ω f.val → D Λ φ = 0 := by
  intro hI N i D
  have hi := (existsUnique_spectralLineTestCompletion (F := F) a hs ω).exists.choose_spec
  constructor
  · let q := spectralSobolevIsotypeQuotient_mk (F := F) a hI hs ω
    have hd : DenseRange (q.comp i) :=
      (spectralSobolevIsotypeQuotient_mk_surjective a hI hs ω).denseRange.comp hi.2.1 q.continuous
    intro Λ₁ Λ₂ hΛ
    apply DFunLike.coe_injective
    exact hd.equalizer Λ₁.continuous Λ₂.continuous
      (funext fun φ ↦ congrArg (fun T : StrongDual ℂ Eω(ω) ↦ T φ) hΛ)
  · intro Λ φ f hφ
    let x : globalPolarFreeThetaSubmodule (F := F) ω :=
      ⟨Submodule.Quotient.mk f.val, Submodule.mem_map.mpr ⟨f.val, f.property, rfl⟩⟩
    let j := (exists_globalHomogeneousThetaSobolevInclusion
      (F := F) (a := a) hI hs ω).choose
    have hj := (exists_globalHomogeneousThetaSobolevInclusion
      (F := F) (a := a) hI hs ω).choose_spec.2.2
    have he : (i φ).val = (j x).val.val := by
      apply Lp.ext
      apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
      have hw : modulationWeight m𝔽 a φ.val.val =ᵐ[μ𝔽]
          modulationWeight m𝔽 a (homogeneousAdelicTheta ω f.val) :=
        Filter.Eventually.of_forall (congrFun (congrArg (modulationWeight m𝔽 a) hφ))
      exact (hi.1 φ).trans (hw.trans (hj f x rfl).2.symm)
    have hn : (i φ).val ∈ Θ(a, hI, hs) := by
      rw [he]
      exact (j x).val.property
    exact (congrArg Λ ((spectralSobolevIsotypeQuotient_mk_eq_zero_iff a hI hs ω (i φ)).mpr hn)).trans
      (map_zero Λ)

end TestDuality

/-- Every logarithmic moment of a function integrable against all quasi-characters is
integrable against every real norm twist. -/
private theorem spectralLineJet_functional_moment
    {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) (χ : QuasiCharacter G) (u : G → ℂ)
    (hu : ∀ c : QuasiCharacter G, Integrable (fun g ↦ u g * c g) μ) (σ : ℝ) (n : ℕ) :
    Integrable (fun g ↦ u g * (Real.log ((m g).val : ℝ) : ℂ) ^ n *
      quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) μ := by
  have hlog : Measurable (fun g ↦ Real.log ((m g).val : ℝ)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable.log
  let tw (w : ℝ) := quasiCharacterNormTwist m.toMonoidHom m.continuous χ (w : ℂ)
  have h1 := (hu (tw (σ + 1))).norm
  have h2 := (hu (tw (σ - 1))).norm
  have hmeas : AEStronglyMeasurable (fun g ↦ u g * (Real.log ((m g).val : ℝ) : ℂ) ^ n *
      quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) μ := by
    have hL : AEStronglyMeasurable (fun g ↦ (Real.log ((m g).val : ℝ) : ℂ) ^ n) μ :=
      ((Complex.measurable_ofReal.comp hlog).pow_const n).aestronglyMeasurable
    refine ((hu (tw σ)).aestronglyMeasurable.mul hL).congr (ae_of_all _ fun g ↦ ?_)
    simp only [Pi.mul_apply, tw]
    ring
  refine ((h1.add h2).const_mul (n.factorial : ℝ)).mono' hmeas (ae_of_all _ fun g ↦ ?_)
  set L := Real.log ((m g).val : ℝ) with hLdef
  have hnorm (w : ℝ) : ‖quasiCharacterNormTwist m.toMonoidHom m.continuous χ (w : ℂ) g‖ =
      ‖χ g‖ * Real.exp (w * L) := by
    rw [quasiCharacterNormTwist_eq_exp, norm_mul, ← Complex.ofReal_mul, Complex.norm_exp_ofReal]
  have hpow : |L| ^ n ≤ n.factorial * (Real.exp L + Real.exp (-L)) := by
    have h := Real.pow_div_factorial_le_exp |L| (abs_nonneg L) n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have habs : Real.exp |L| ≤ Real.exp L + Real.exp (-L) := by
      rcases abs_cases L with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [h'] <;>
        linarith [Real.exp_pos L, Real.exp_pos (-L)]
    rw [div_le_iff₀ hf] at h
    nlinarith
  change ‖u g * (L : ℂ) ^ n * tw σ g‖ ≤
    (n.factorial : ℝ) * (‖u g * tw (σ + 1) g‖ + ‖u g * tw (σ - 1) g‖)
  simp only [tw, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, hnorm]
  have hA : 0 ≤ ‖u g‖ * (‖χ g‖ * Real.exp (σ * L)) := by positivity
  have e1 : Real.exp ((σ + 1) * L) = Real.exp (σ * L) * Real.exp L := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp ((σ - 1) * L) = Real.exp (σ * L) * Real.exp (-L) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, e2]
  calc ‖u g‖ * |L| ^ n * (‖χ g‖ * Real.exp (σ * L))
      = (‖u g‖ * (‖χ g‖ * Real.exp (σ * L))) * |L| ^ n := by ring
    _ ≤ (‖u g‖ * (‖χ g‖ * Real.exp (σ * L))) * (n.factorial * (Real.exp L + Real.exp (-L))) :=
        mul_le_mul_of_nonneg_left hpow hA
    _ = _ := by ring

/-- The pairing of a weighted function with a line jet is the derivative of its
norm-twisted Mellin integral at the shifted point. -/
private theorem spectralLineJet_functional_deriv
    {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) (χ : QuasiCharacter G) (u : G → ℂ)
    (hu : ∀ c : QuasiCharacter G, Integrable (fun g ↦ u g * c g) μ) (a t : ℝ) (k : ℕ) :
    ∫ g, modulationWeight m a u g *
        (quasiCharacterNormTwist m.toMonoidHom m.continuous χ (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) g *
          (Real.log ((m g).val : ℝ) : ℂ) ^ k) ∂μ =
      iteratedDeriv k (fun w ↦ ∫ g, u g *
        quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g ∂μ)
        ((a : ℂ) + (t : ℂ) * Complex.I) := by
  obtain ⟨_, _, hderiv⟩ := iteratedDeriv_normTwist_moment m μ χ
    (α := a - 1) (β := a + 1) (fun σ _ n ↦ spectralLineJet_functional_moment m μ χ u hu σ n) k
    (z := (a : ℂ) + (t : ℂ) * Complex.I) (by simp)
  rw [hderiv]
  refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
  have hpos : 0 < ((m g).val : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero (m g).ne_zero)
  change (((((m g).val : ℝ) ^ a : ℝ)) : ℂ) * u g * _ = _
  dsimp only
  rw [quasiCharacterNormTwist_eq_exp, quasiCharacterNormTwist_eq_exp,
    Real.rpow_def_of_pos hpos, Complex.ofReal_exp, Complex.ofReal_mul]
  have e : Complex.exp (((a : ℂ) + (t : ℂ) * Complex.I) * (Real.log ((m g).val : ℝ) : ℂ)) =
      Complex.exp ((Real.log ((m g).val : ℝ) : ℂ) * (a : ℂ)) *
        Complex.exp ((((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) * (Real.log ((m g).val : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]
  ring


/-- Every function in the two-sided decay space is integrable against every quasi-character. -/
private theorem spectralLineJet_functional_integrable
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (μ : Measure G) [μ.IsHaarMeasure] (φ : ModulatedExponentialDecay m univ)
    (c : QuasiCharacter G) : Integrable (fun g ↦ φ.val g * c g) μ :=
  modulatedFourierMellin_integrable m univ hm ordConnected_univ univ_nonempty μ isOpen_univ hms φ
    ⟨c, mem_univ _⟩

/-- Paper: (10.2.1.9), p. 442. A surviving line jet acts on the Sobolev
space by the integral of the input against that jet. On a weighted exponential-
decay test this is precisely the derivative in the existing Mellin chart. -/
theorem spectralLineJet_functional (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a s : ℝ} (hs : 1 < s) (j : SpectralLineJetIndex χ a s) :
    ∃ Λ : StrongDual ℂ W(0, 0, s),
      (∀ f : W(0, 0, s), Integrable (fun g ↦ f g * lineJet(χ, j) g) μ𝔽 ∧
        Λ f = ∫ g, f g * lineJet(χ, j) g ∂μ𝔽) ∧
      ∀ (φ : ModulatedExponentialDecay m𝔽 univ) (f : W(0, 0, s)),
        (f : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a φ.val →
        Λ f = iteratedDeriv j.val.2.2 (fun z ↦ modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽
          φ.val (ideleClassNormTwist (χ j.val.1) z)) (shift(a, j.val.2.1)) := by
  have hs0 : (0 : ℝ) ≤ s := by linarith
  let Td := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 0 0 s le_rfl hs0).exists.choose
  let u : W'(0, 0, s) := (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))
  have hac : μ𝔽 ≪ L2μ'(0, 0, s) := by
    refine withDensity_absolutelyContinuous' ?_ (ae_of_all _ fun g ↦ ?_)
    · exact ((continuous_intervalSobolevDensity' 0 0 s).measurable.comp
        (NNReal.continuous_coe.comp (Units.continuous_val.comp
          (isProperMap_ideleClassNorm F).continuous)).measurable.log).inv.ennreal_ofReal.aemeasurable
    · exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (intervalSobolevDensity_pos 0 0 s _))
  have hae : (u : C𝔽 → ℂ) =ᵐ[μ𝔽] lineJet(χ, j) := hac.ae_le (MemLp.coeFn_toLp _)
  have hpair (f : W(0, 0, s)) : Integrable (fun g ↦ f g * lineJet(χ, j) g) μ𝔽 ∧
      Td.symm u f = ∫ g, f g * lineJet(χ, j) g ∂μ𝔽 := by
    have h := spectralSobolevPairing_dual le_rfl hs0 (Td.symm u) f
    have hTu : Td (Td.symm u) = u := Td.apply_symm_apply u
    have hc : (fun g ↦ f g * Td (Td.symm u) g) =ᵐ[μ𝔽] fun g ↦ f g * lineJet(χ, j) g := by
      rw [hTu]
      exact hae.mono fun g hg ↦ congrArg (f g * ·) hg
    exact ⟨h.1.congr hc, h.2.trans (integral_congr_ae hc)⟩
  refine ⟨Td.symm u, hpair, fun φ f hf ↦ ?_⟩
  let χq : QuasiCharacter C𝔽 :=
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ j.val.1)
  have hc : (fun g ↦ f g * lineJet(χ, j) g) =ᵐ[μ𝔽]
      fun g ↦ modulationWeight m𝔽 a φ.val g *
        (quasiCharacterNormTwist (m𝔽).toMonoidHom (m𝔽).continuous χq (shift(0, j.val.2.1)) g *
          (Real.log ((m𝔽 g).val : ℝ) : ℂ) ^ j.val.2.2) :=
    hf.mono fun g hg ↦ by dsimp only; rw [hg]; rfl
  have key := spectralLineJet_functional_deriv m𝔽 μ𝔽 χq φ.val
    (spectralLineJet_functional_integrable m𝔽 hm𝔽 hms𝔽 μ𝔽 φ) a j.val.2.1 j.val.2.2
  have hF : (fun z ↦ modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 φ.val
      (ideleClassNormTwist (χ j.val.1) z)) = fun w ↦ ∫ g, φ.val g *
        quasiCharacterNormTwist (m𝔽).toMonoidHom (m𝔽).continuous χq w g ∂μ𝔽 :=
    funext fun z ↦ modulatedFourierMellin_univ m𝔽 hm𝔽 μ𝔽 _ _
  rw [(hpair f).2, integral_congr_ae hc, hF]
  exact key

section

universe u v

/-- Integrating scalar multiples of a commutative action preserves every eigenspace. -/
private theorem spectral_integrated_action_eigenvector
    {G : Type u} [CommGroup G] [MeasurableSpace G] (μ : Measure G)
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ρ : G →* (V →L[ℂ] V)) (f : G → ℂ) (u v : V)
    (hv : HasPettisIntegral (.positive μ) (fun g ↦ f g • ρ g u) v)
    (k : G) (c : ℂ) (hu : ρ k u = c • u) : ρ k v = c • v := by
  have hev (δ : StrongDual ℂ V) : δ v = ∫ g, δ (f g • ρ g u) ∂μ :=
    congrArg (fun z : PettisWeakCompletion V ↦
      (show Module.Dual ℂ (StrongDual ℂ V) from z) δ) hv.2
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro δ
  have he (g : G) : ρ k (f g • ρ g u) = c • (f g • ρ g u) := by
    rw [map_smul]
    have hc : ρ k (ρ g u) = ρ g (ρ k u) := by
      change (ρ k * ρ g) u = (ρ g * ρ k) u
      rw [← map_mul, ← map_mul, mul_comm k g]
    rw [hc, hu, map_smul, smul_comm]
  calc
    δ (ρ k v) = ∫ g, δ (ρ k (f g • ρ g u)) ∂μ :=
      hev (δ.comp (ρ k))
    _ = ∫ g, c • δ (f g • ρ g u) ∂μ :=
      integral_congr_ae (.of_forall fun g ↦ (congrArg δ (he g)).trans (map_smul δ c _))
    _ = c • δ v := by rw [integral_smul, ← hev δ]
    _ = δ (c • v) := (map_smul δ c v).symm

end

/-- Paper: (10.2.1.10), pp. 442–443. The band-limited approximate unit acts
by convolution on the fixed norm-one isotype and converges there strongly.
Deviation: The Fourier band is centered on the inverse lift for the
left-translation convention of §9.3. -/
theorem exists_spectralLineIsotypeConvolution (χ : PontryaginDual C𝔽) {s : ℝ} (hs : 0 ≤ s) :
    let hI : (0 : ℝ) ≤ 0 := le_rfl
    let E := Wω(hI, hs, χ.comp restriction)
    let A := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose
    ∃ (φ : ℕ → SchwartzBruhat C𝔽) (P : ℕ → (E →L[ℂ] E)),
      (∀ n, ‖A (φ n)‖ ≤ 2) ∧
      (∀ n (k : C₁) g, (φ n) (k.val⁻¹ * g) = (χ k.val : ℂ) * (φ n) g) ∧
      (∀ n, tsupport (lcaFourier μ𝔽 (φ n)) ⊆
        modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n) ∧
      (∀ n (f : E), (P n f).val = A (φ n) f.val) ∧
      ∀ f : E, Tendsto (fun n ↦ P n f) atTop (𝓝 f) := by
  intro hI E A
  let τ := hardySobolevTranslation μ𝔽 m𝔽 0 0 s hI hs
  let B := (existsUnique_singletonDecay_lineAction μ𝔽 m𝔽 hm𝔽 hms𝔽 0 s hs).exists.choose
  have hB := (existsUnique_singletonDecay_lineAction μ𝔽 m𝔽 hm𝔽 hms𝔽 0 s hs).exists.choose_spec.1
  have hA := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose_spec
  let e := (modulatedExponentialDecay_singleton_schwartz m𝔽 hm𝔽 hms𝔽 0).choose
  have he (f : ModulatedExponentialDecay m𝔽 {0}) : (e f : C𝔽 → ℂ) = f.val := by
    exact ((modulatedExponentialDecay_singleton_schwartz m𝔽 hm𝔽 hms𝔽 0).choose_spec f).trans
      (modulationWeight_zero m𝔽 f.val)
  have hAB (f : ModulatedExponentialDecay m𝔽 {0}) : A (e f) = B f := by
    apply ContinuousLinearMap.ext
    intro u
    have hp : (fun g ↦ (e f).val g • τ g u) = (fun g ↦ f.val g • τ g u) :=
      funext fun g ↦ congrArg (fun z : ℂ ↦ z • τ g u) (congrFun (he f) g)
    have hP : HasPettisIntegral (.positive μ𝔽) (fun g ↦ f.val g • τ g u) (A (e f) u) :=
      hp ▸ hA (e f) u
    exact hP.unique (hB f u)
  let φ := (exists_singletonDecay_isotype_approximation μ𝔽 m𝔽 hm𝔽 hms𝔽 0 s hs χ⁻¹).choose
  have hφ := (exists_singletonDecay_isotype_approximation μ𝔽 m𝔽 hm𝔽 hms𝔽 0 s hs χ⁻¹).choose_spec
  have hmem (n : ℕ) (u : E) : A (e (φ n)) u.val ∈ E := by
    apply (mem_actionIsotype _ _ _).mpr
    intro k
    exact spectral_integrated_action_eigenvector μ𝔽 τ (e (φ n)).val u.val
      (A (e (φ n)) u.val) (hA (e (φ n)) u.val) k.val (χ k.val : ℂ)
      ((mem_actionIsotype _ _ _).mp u.property k)
  let P (n : ℕ) : E →L[ℂ] E :=
    ((A (e (φ n))).comp E.subtypeL).codRestrict E (hmem n)
  refine ⟨fun n ↦ e (φ n), P, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [hAB]
    exact hφ.1 n
  · intro n k g
    have hchar : star ((χ⁻¹) k.val : ℂ) = (χ k.val : ℂ) := by
      change star (((χ k.val)⁻¹ : Circle) : ℂ) = _
      rw [Circle.coe_inv_eq_conj]
      exact star_star _
    calc
      e (φ n) (k.val⁻¹ * g) = (φ n).val (k.val⁻¹ * g) := congrFun (he (φ n)) _
      _ = star ((χ⁻¹) k.val : ℂ) * (φ n).val g := hφ.2.1 n k g
      _ = (χ k.val : ℂ) * e (φ n) g := congrArg₂ (· * ·) hchar (congrFun (he (φ n)) g).symm
  · intro n
    simpa only [he, modulationWeight_zero] using hφ.2.2.1 n
  · intro n f
    rfl
  · intro f
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun n ↦ A (e (φ n)) f.val) atTop (𝓝 f.val)
    have h : Tendsto (fun n ↦ B (φ n) f.val) atTop (𝓝 f.val) :=
      hφ.2.2.2 ⟨f.val, by simpa only [inv_inv] using f.property⟩
    exact h.congr' (Filter.Eventually.of_forall fun n ↦
      congrArg (fun T : W(0, 0, s) →L[ℂ] W(0, 0, s) ↦ T f.val) (hAB (φ n)).symm)

private theorem spectralJet_lp_norm_sq {μ : Measure C𝔽} (u : Lp ℂ 2 μ) :
    ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂μ := by
  have hre : (inner ℂ u u).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  rw [← hre, L2.inner_def]
  have hre_int : (∫ g : C𝔽, inner ℂ (u g) (u g) ∂μ).re =
      ∫ g : C𝔽, (inner ℂ (u g) (u g)).re ∂μ :=
    (Complex.reCLM.integral_comp_comm (L2.integrable_inner u u)).symm
  rw [hre_int]
  refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (u g)

private theorem spectralZeroJet_continuous (χ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) :
    Continuous (spectralZeroJet χ b t k) :=
  (ideleClassNormTwist χ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I)).continuous.mul
    ((Complex.continuous_ofReal.comp (continuous_logModule' m𝔽)).pow k)

private theorem spectralZeroJet_norm_sq (χ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (g : C𝔽) :
    ‖spectralZeroJet χ b t k g‖ ^ 2 = Real.exp (2 * b * logNorm g) * (logNorm g) ^ (2 * k) := by
  have hpos : 0 < ((ideleClassNorm F g).val : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have htwist : ‖ideleClassNormTwist χ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I) g‖ =
      Real.exp (b * logNorm g) := by
    change ‖(χ g : ℂ) *
      (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Real.rpow_def_of_pos hpos,
      mul_comm]
  change ‖ideleClassNormTwist χ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I) g *
    (logNorm g : ℂ) ^ k‖ ^ 2 = _
  rw [norm_mul, htwist, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hexp : Real.exp (b * logNorm g) ^ 2 = Real.exp (2 * b * logNorm g) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hpow : (|logNorm g| ^ k) ^ 2 = (logNorm g) ^ (2 * k) := by
    calc
      (|logNorm g| ^ k) ^ 2 = (|logNorm g| ^ 2) ^ k := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
      _ = ((logNorm g) ^ 2) ^ k := congrArg (fun y : ℝ ↦ y ^ k) (sq_abs (logNorm g))
      _ = (logNorm g) ^ (2 * k) := (pow_mul _ _ _).symm
  rw [hexp, hpow]

private theorem symmIntervalSobolevDensity_eq {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    intervalSobolevDensity (-α) α s x = Real.exp (2 * α * |x|) * (1 + x ^ 2) ^ (s / 2) := by
  unfold intervalSobolevDensity
  congr 1
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_right]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [abs_of_nonpos hx, max_eq_left]
    · congr 1
      ring
    · exact Real.exp_le_exp.mpr (by nlinarith)

private theorem symmIntervalSobolevDensity_pos {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    0 < intervalSobolevDensity (-α) α s x := by
  rw [symmIntervalSobolevDensity_eq hα]
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)

private theorem symmIntervalSobolevDensity_inv_continuous {α : ℝ} (hα : 0 ≤ α) (s : ℝ) :
    Continuous (fun g : C𝔽 ↦ (intervalSobolevDensity (-α) α s (logNorm g))⁻¹) := by
  have hρ : Continuous (fun g : C𝔽 ↦ intervalSobolevDensity (-α) α s (logNorm g)) := by
    have heq : (fun g : C𝔽 ↦ intervalSobolevDensity (-α) α s (logNorm g)) =
        fun g : C𝔽 ↦ Real.exp (2 * α * |logNorm g|) * (1 + (logNorm g) ^ 2) ^ (s / 2) :=
      funext fun g ↦ symmIntervalSobolevDensity_eq hα s (logNorm g)
    rw [heq]
    exact (Real.continuous_exp.comp (continuous_const.mul (continuous_logModule' m𝔽).abs)).mul
      (((continuous_const : Continuous (fun _ : C𝔽 ↦ (1 : ℝ))).add
        ((continuous_logModule' m𝔽).pow 2)).rpow_const fun g ↦ Or.inl (by
          change (1 : ℝ) + (logNorm g) ^ 2 ≠ 0
          positivity))
  exact hρ.inv₀ fun g ↦ (symmIntervalSobolevDensity_pos hα s (logNorm g)).ne'

private theorem pow_mul_rpow_inv_continuous (k : ℕ) (s : ℝ) :
    Continuous (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
  (continuous_id.pow (2 * k)).mul
    (((continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
        Or.inl (by change (1 : ℝ) + x ^ 2 ≠ 0; positivity)).inv₀ fun x ↦
      (Real.rpow_pos_of_pos (by change (0 : ℝ) < 1 + x ^ 2; positivity) _).ne')

private theorem spectralLineJet_integral_pos {s : ℝ} (hs : 1 < s) {k : ℕ}
    (hkN : k < Nat.ceil ((s - 1) / 2)) :
    0 < ∫ g : C𝔽, (logNorm g) ^ (2 * k) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ ∂μ𝔽 := by
  have hk' : (k : ℝ) < (s - 1) / 2 := Nat.lt_ceil.mp hkN
  have hk : 2 * (k : ℝ) + 1 < s := by linarith
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let fk : ℝ → ℝ := fun x ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹
  have hfk_int : Integrable fk volume := integrable_pow_mul_rpow_inv hk
  have hmp : MeasurePreserving (fun g : C𝔽 ↦ logNorm g) ν volume :=
    sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have hlogm : AEMeasurable (fun g : C𝔽 ↦ logNorm g) ν :=
    (continuous_logModule' m𝔽).measurable.aemeasurable
  have hν_eq : ∫ g : C𝔽, fk (logNorm g) ∂ν = ∫ x : ℝ, fk x ∂volume := by
    rw [← hmp.map_eq,
      integral_map hlogm (pow_mul_rpow_inv_continuous k s).aestronglyMeasurable]
  have hvol_pos : 0 < ∫ x : ℝ, fk x ∂volume := by
    let c : ℝ := ((5 : ℝ) ^ (s / 2))⁻¹
    have hc : 0 < c := inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    have hind_int : Integrable ((Icc (1 : ℝ) 2).indicator fun _ ↦ c) volume :=
      (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    have hle : ∀ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c) x ≤ fk x := by
      intro x
      by_cases hx : x ∈ Icc (1 : ℝ) 2
      · rw [indicator_of_mem hx]
        have hpow : (1 : ℝ) ≤ x ^ (2 * k) := one_le_pow₀ hx.1
        have hbase : 1 + x ^ 2 ≤ 5 := by nlinarith [hx.1, hx.2]
        have hrpow : (1 + x ^ 2) ^ (s / 2) ≤ (5 : ℝ) ^ (s / 2) :=
          Real.rpow_le_rpow (by positivity) hbase (by linarith)
        have hinv : c ≤ ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
          inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) hrpow
        calc
          c = 1 * c := (one_mul c).symm
          _ ≤ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
            mul_le_mul hpow hinv hc.le (by positivity)
      · rw [indicator_of_notMem hx]
        exact mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
          (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    have hint_le : ∫ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c) x ∂volume ≤
        ∫ x : ℝ, fk x ∂volume :=
      integral_mono hind_int hfk_int hle
    have hind_val : ∫ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c) x ∂volume = c := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc]
      norm_num
    linarith
  have hμ_eq : (∫ g : C𝔽, fk (logNorm g) ∂μ𝔽) =
      (Measure.haarScalarFactor μ𝔽 ν : ℝ) * ∫ x : ℝ, fk x ∂volume := by
    conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, hν_eq]
  change 0 < ∫ g : C𝔽, fk (logNorm g) ∂μ𝔽
  rw [hμ_eq]
  have hfac_pos : 0 < (Measure.haarScalarFactor μ𝔽 ν : ℝ) := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν)
  exact mul_pos hfac_pos hvol_pos

/-- Paper: Proposition 10.2.1.3 and (10.2.1.12), p. 443. A single annulus
contains all the a-line jet classes.
Deviation: Use the truncated multiplicity intended by the reference to
(10.2.1.6). The lower bound asserts disjointness from the open ball, which
also makes sense for an empty zero set. -/
theorem spectralLineJet_annulus (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : SpectralLineJetIndex χ a s,
      let u := (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))
      C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C := by
  let N : ℕ := Nat.ceil ((s - 1) / 2)
  let I : ℕ → ℝ := fun k ↦
    ∫ g : C𝔽, (logNorm g) ^ (2 * k) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ ∂μ𝔽
  let r : ℕ → ℝ := fun k ↦ Real.sqrt (I k)
  have hnorm_sq : ∀ j : SpectralLineJetIndex χ a s,
      ‖(spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))‖ ^ 2 = I j.val.2.2 := by
    intro j
    let u := (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))
    have h1 : ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(0, 0, s)) := spectralJet_lp_norm_sq u
    have h2 : ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(0, 0, s)) =
        ∫ g : C𝔽, (logNorm g) ^ (2 * j.val.2.2) ∂(L2μ'(0, 0, s)) := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (spectralLineJet_memLp χ hs j)] with g hg
      rw [hg, spectralZeroJet_norm_sq]
      simp
    have h3 : ∫ g : C𝔽, (logNorm g) ^ (2 * j.val.2.2) ∂(L2μ'(0, 0, s)) = I j.val.2.2 := by
      have hdens : Continuous (fun g : C𝔽 ↦ (intervalSobolevDensity 0 0 s (logNorm g))⁻¹) := by
        simpa only [neg_zero] using symmIntervalSobolevDensity_inv_continuous (F := F) le_rfl s
      rw [integral_withDensity_eq_integral_toReal_smul hdens.measurable.ennreal_ofReal
        (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (ae_of_all μ𝔽 fun g ↦ ?_)
      dsimp only
      have hdeq : (intervalSobolevDensity 0 0 s (logNorm g))⁻¹ =
          ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ := by
        simp only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]
      rw [smul_eq_mul, hdeq,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le),
        mul_comm]
    exact h1.trans (h2.trans h3)
  let C : ℝ := 1 + ∑ k ∈ Finset.range N, (r k + (r k)⁻¹)
  have hC_pos : 0 < C := by
    have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.range N, (r k + (r k)⁻¹) :=
      Finset.sum_nonneg fun k _ ↦ add_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    linarith
  refine ⟨C, hC_pos, fun j ↦ ?_⟩
  have hjN : j.val.2.2 ∈ Finset.range N :=
    Finset.mem_range.mpr (lt_of_lt_of_le j.property (min_le_right _ _))
  have hr_pos : 0 < r j.val.2.2 :=
    Real.sqrt_pos.mpr (spectralLineJet_integral_pos hs (Finset.mem_range.mp hjN))
  have hnorm_eq : ‖(spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))‖ = r j.val.2.2 := by
    rw [← Real.sqrt_sq (norm_nonneg _), hnorm_sq j]
  have hterm_le : r j.val.2.2 + (r j.val.2.2)⁻¹ ≤ C := by
    have h1 : r j.val.2.2 + (r j.val.2.2)⁻¹ ≤ ∑ k ∈ Finset.range N, (r k + (r k)⁻¹) :=
      Finset.single_le_sum
        (fun k _ ↦ add_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))) hjN
    linarith
  dsimp only
  rw [hnorm_eq]
  refine ⟨?_, by linarith [inv_pos.mpr hr_pos]⟩
  have hinv_le : (r j.val.2.2)⁻¹ ≤ C := by linarith
  calc
    C⁻¹ ≤ ((r j.val.2.2)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hr_pos) hinv_le
    _ = r j.val.2.2 := inv_inv _

/-- Paper: Terminology 10.2.1.2, p. 444. A regular family has norms bounded
away from zero. -/
def IsRegularSpectralFamily {ι E : Type*} [Norm E] (x : ι → E) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ ‖x i‖

/-- Paper: Terminology 10.2.1.2, p. 444. A family is normalized if its
norms are bounded above and the family is regular. -/
def IsNormalizedSpectralFamily {ι E : Type*} [Norm E] (x : ι → E) : Prop :=
  (∃ C : ℝ, ∀ i, ‖x i‖ ≤ C) ∧ IsRegularSpectralFamily x

/-- Paper: Terminology 10.2.1.2, p. 444. On normed-space sequences the
two conditions agree with the existing §4.1 terminology. -/
theorem spectralFamily_regular_normalized_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (x : ℕ → E) :
    (IsRegularSpectralFamily x ↔ SchauderBasis.IsRegular x) ∧
    (IsNormalizedSpectralFamily x ↔ SchauderBasis.IsNormalized x) := by
  have hr : IsRegularSpectralFamily x ↔ SchauderBasis.IsRegular x := by
    constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨Metric.ball 0 c, Metric.ball_mem_nhds _ hc, fun n hn ↦
        (h n).not_gt (by simpa only [Metric.mem_ball, dist_zero_right] using hn)⟩
    · rintro ⟨U, hU, hx⟩
      obtain ⟨c, hc, hball⟩ := Metric.mem_nhds_iff.mp hU
      refine ⟨c, hc, fun n ↦ le_of_not_gt fun hn ↦ hx n (hball ?_)⟩
      simpa only [Metric.mem_ball, dist_zero_right] using hn
  refine ⟨hr, ?_⟩
  simp only [IsNormalizedSpectralFamily, SchauderBasis.IsNormalized, ← hr,
    NormedSpace.isVonNBounded_iff' ℂ, Set.forall_mem_range]
  exact and_comm

/-- Paper: Terminology 10.2.1.2, p. 444. A nonzero vector defines a regular
and normalized singleton family.
Deviation: Sanity check for the two predicates. -/
theorem spectralFamily_singleton_normalized {E : Type*} [NormedAddCommGroup E] (x : E)
    (_hx : x ≠ 0) : IsNormalizedSpectralFamily (fun _ : Unit ↦ x) := by
  exact ⟨⟨‖x‖, fun _ ↦ le_rfl⟩, ‖x‖, norm_pos_iff.mpr _hx, fun _ ↦ le_rfl⟩

-- TODO(paper-gap): The general claim about the Schauder property on p. 444
-- lacks a proof. The primal normalization invoked again on p. 451 is false:
-- close simple critical-line zeta zeros give jets at distance tending to zero,
-- so the corresponding biorthogonal vector norms are unbounded (ERRATA R5).

section BandProjections

attribute [local instance] instDualMeasurableSpaceSec3

/-- Orthogonal projections onto closures of subspaces converge strongly whenever each
vector has a convergent sequence of approximants in the corresponding subspaces. -/
private theorem spectralLineIsotype_bandProjections_of_approximants
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (S : ℕ → Submodule ℂ Q)
    (happrox : ∀ q : Q, ∃ y : ℕ → Q,
      (∀ n, y n ∈ S n) ∧ Tendsto y atTop (𝓝 q)) :
    ∃ P : ℕ → (Q →L[ℂ] Q),
      (∀ n, Set.range (P n) = closure (S n : Set Q)) ∧
      (∀ n q y, y ∈ closure (S n : Set Q) → ‖q - P n q‖ ≤ ‖q - y‖) ∧
      ∀ q, Tendsto (fun n ↦ P n q) atTop (𝓝 q) := by
  let C (n : ℕ) := (S n).topologicalClosure
  let : ∀ n, CompleteSpace (C n) := fun n ↦
    (Submodule.isClosed_topologicalClosure (S n)).completeSpace_coe
  let P (n : ℕ) : Q →L[ℂ] Q := (C n).starProjection
  have hmin (n : ℕ) (q y : Q) (hy : y ∈ closure (S n : Set Q)) :
      ‖q - P n q‖ ≤ ‖q - y‖ := by
    change ‖q - (C n).starProjection q‖ ≤ ‖q - y‖
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩
      (⟨y, hy⟩ : C n)
  refine ⟨P, ?_, hmin, ?_⟩
  · intro n
    change ((C n).starProjection.range : Set Q) = closure (S n : Set Q)
    rw [Submodule.range_starProjection]
    rfl
  · intro q
    obtain ⟨y, hy, hlim⟩ := happrox q
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_)
      (tendsto_iff_dist_tendsto_zero.mp hlim)
    calc
      dist (P n q) q = ‖q - P n q‖ := by
        simpa only [dist_eq_norm] using norm_sub_rev (P n q) q
      _ ≤ ‖q - y n‖ := hmin n q (y n) (subset_closure (hy n))
      _ = dist (y n) q := by
        simpa only [dist_eq_norm] using norm_sub_rev q (y n)

/-- A Fourier band defines a submodule, and its image under a linear quotient map
agrees with the description using any almost-everywhere equal L² representative. -/
private theorem spectralLineIsotype_bandProjections_band_submodule
    {X Y E Q : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup Q] [Module ℂ Q]
    (μ : Measure X) (ν : Measure Y)
    (r : E → X → ℂ) (J : E →ₗ[ℂ] Lp ℂ 2 μ)
    (hJ : ∀ f, (J f : X → ℂ) =ᵐ[μ] r f)
    (q : E →ₗ[ℂ] Q) (U : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν) (band : Set Y) :
    ∃ S : Submodule ℂ Q, (S : Set Q) =
      {z : Q | ∃ f : E, z = q f ∧ ∃ u : Lp ℂ 2 μ,
        (u : X → ℂ) =ᵐ[μ] r f ∧ ∀ᵐ ψ ∂ν, ψ ∉ band → U u ψ = 0} := by
  let A : Submodule ℂ (Lp ℂ 2 ν) := {
    carrier := {v | ∀ᵐ ψ ∂ν, ψ ∉ band → v ψ = 0}
    zero_mem' := by
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := ν)] with ψ hψ
      exact fun _ ↦ hψ
    add_mem' := by
      intro v w hv hw
      change ∀ᵐ ψ ∂ν, ψ ∉ band → (v + w) ψ = 0
      filter_upwards [Lp.coeFn_add v w, hv, hw] with ψ hψ hvψ hwψ
      intro hψband
      rw [hψ, Pi.add_apply, hvψ hψband, hwψ hψband, add_zero]
    smul_mem' := by
      intro c v hv
      change ∀ᵐ ψ ∂ν, ψ ∉ band → (c • v) ψ = 0
      filter_upwards [Lp.coeFn_smul c v, hv] with ψ hψ hvψ
      intro hψband
      rw [hψ, Pi.smul_apply, hvψ hψband, smul_zero]
  }
  refine ⟨(A.comap (U.comp J)).map q, ?_⟩
  ext z
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, rfl, J f, hJ f, hf⟩
  · rintro ⟨f, rfl, u, hu, hUu⟩
    refine ⟨f, ?_, rfl⟩
    have heq : u = J f := Lp.ext (hu.trans (hJ f).symm)
    change ∀ᵐ ψ ∂ν, ψ ∉ band → U (J f) ψ = 0
    simpa only [heq] using hUu

/-- Set-valued version of the projection argument, allowing the Fourier-band submodules
to be constructed independently from their concrete sets. -/
private theorem spectralLineIsotype_bandProjections_of_sets
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (B : ℕ → Set Q) (hsub : ∀ n, ∃ S : Submodule ℂ Q, (S : Set Q) = B n)
    (happrox : ∀ q : Q, ∃ y : ℕ → Q,
      (∀ n, y n ∈ B n) ∧ Tendsto y atTop (𝓝 q)) :
    ∃ P : ℕ → (Q →L[ℂ] Q),
      (∀ n, Set.range (P n) = closure (B n)) ∧
      (∀ n q y, y ∈ closure (B n) → ‖q - P n q‖ ≤ ‖q - y‖) ∧
      ∀ q, Tendsto (fun n ↦ P n q) atTop (𝓝 q) := by
  choose S hS using hsub
  have happrox' : ∀ q : Q, ∃ y : ℕ → Q,
      (∀ n, y n ∈ S n) ∧ Tendsto y atTop (𝓝 q) := by
    intro q
    obtain ⟨y, hy, hlim⟩ := happrox q
    refine ⟨y, fun n ↦ ?_, hlim⟩
    change y n ∈ (S n : Set Q)
    rw [hS n]
    exact hy n
  obtain ⟨P, hrange, hmin, hlim⟩ :=
    spectralLineIsotype_bandProjections_of_approximants S happrox'
  refine ⟨P, fun n ↦ ?_, fun n q y hy ↦ ?_, hlim⟩
  · simpa only [hS n] using hrange n
  · apply hmin n q y
    simpa only [hS n] using hy

/-- A surjective continuous linear image of supported approximants admits strongly
convergent orthogonal projections onto the closures of the corresponding bands. -/
private theorem spectralLineIsotype_bandProjections_of_supported_approximants
    {X Y E Q : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (μ : Measure X) (ν : Measure Y)
    (r : E → X → ℂ) (J : E →ₗ[ℂ] Lp ℂ 2 μ)
    (hJ : ∀ f, (J f : X → ℂ) =ᵐ[μ] r f)
    (q : E →L[ℂ] Q) (hq : Surjective q)
    (U : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν) (band : ℕ → Set Y)
    (R : ℕ → E → E)
    (hsupport : ∀ n f, ∀ᵐ ψ ∂ν, ψ ∉ band n → U (J (R n f)) ψ = 0)
    (hlim : ∀ f, Tendsto (fun n ↦ R n f) atTop (𝓝 f)) :
    let B (n : ℕ) := {z : Q | ∃ f : E, z = q f ∧ ∃ u : Lp ℂ 2 μ,
      (u : X → ℂ) =ᵐ[μ] r f ∧ ∀ᵐ ψ ∂ν, ψ ∉ band n → U u ψ = 0}
    ∃ P : ℕ → (Q →L[ℂ] Q),
      (∀ n, Set.range (P n) = closure (B n)) ∧
      (∀ n z y, y ∈ closure (B n) → ‖z - P n z‖ ≤ ‖z - y‖) ∧
      ∀ z, Tendsto (fun n ↦ P n z) atTop (𝓝 z) := by
  intro B
  have hmem (n : ℕ) (f : E) : q (R n f) ∈ B n :=
    ⟨R n f, rfl, J (R n f), hJ (R n f), hsupport n f⟩
  have happrox (z : Q) : ∃ y : ℕ → Q,
      (∀ n, y n ∈ B n) ∧ Tendsto y atTop (𝓝 z) := by
    obtain ⟨f, rfl⟩ := hq z
    refine ⟨fun n ↦ q (R n f), fun n ↦ hmem n f, ?_⟩
    exact q.continuous.continuousAt.tendsto.comp (hlim f)
  have hsub (n : ℕ) : ∃ S : Submodule ℂ Q, (S : Set Q) = B n := by
    exact spectralLineIsotype_bandProjections_band_submodule μ ν r J hJ
      q.toLinearMap U (band n)
  exact spectralLineIsotype_bandProjections_of_sets B hsub happrox

private theorem spectralLineIsotype_bandProjections_support_closed
    {X : Type*} [MeasurableSpace X] (ν : Measure X) (S : Set X)
    (hS : MeasurableSet S) :
    IsClosed {f : Lp ℂ 2 ν | ∀ᵐ x ∂ν, x ∉ S → f x = 0} := by
  obtain ⟨P, -, hP⟩ := hardySobolevCutoff_spec (μ := ν) hS
  have hset : {f : Lp ℂ 2 ν | ∀ᵐ x ∂ν, x ∉ S → f x = 0} =
      {f : Lp ℂ 2 ν | P f = f} := by
    ext f
    constructor
    · intro hf
      apply Lp.ext
      filter_upwards [(hP f).2.2, hf] with x hx hfx
      rw [hx]
      by_cases hxs : x ∈ S
      · exact Set.indicator_of_mem hxs _
      · rw [Set.indicator_of_notMem hxs, hfx hxs]
    · intro hf
      filter_upwards [(hP f).2.2] with x hx
      intro hxs
      rw [hf] at hx
      exact hx.trans (Set.indicator_of_notMem hxs _)
  rw [hset]
  exact isClosed_eq P.continuous continuous_id

private theorem spectralLineIsotype_bandProjections_dense_integrable
    {G : Type*} [TopologicalSpace G] [T2Space G] [LocallyCompactSpace G]
    [NormalSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ w : Measure G)
    [IsLocallyFiniteMeasure μ] [w.Regular] (hle : μ ≤ w) :
    Dense {u : Lp ℂ 2 w | Integrable (u : G → ℂ) μ} := by
  intro u
  apply EMetric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨r, hr, hlt⟩ := exists_between hε
  obtain ⟨f, hc, he, hf, hm⟩ :=
    (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le (by simp) hr.ne'
  refine ⟨hm.toLp f,
    (hf.integrable_of_hasCompactSupport hc).congr (ae_mono hle hm.coeFn_toLp.symm), ?_⟩
  rw [Lp.edist_def, eLpNorm_congr_ae (EventuallyEq.rfl.sub hm.coeFn_toLp)]
  exact he.trans_lt hlt

private theorem spectralLineIsotype_bandProjections_convolution_support
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure (PontryaginDual G))
    (hν : IsLCAPlancherelMeasure μ ν) (w : Measure G) [w.Regular]
    (hle : μ ≤ w) (J : Lp ℂ 2 w →L[ℂ] Lp ℂ 2 μ)
    (hJ : ∀ u, (J u : G → ℂ) =ᵐ[μ] (u : G → ℂ))
    (τ : G →* (Lp ℂ 2 w →L[ℂ] Lp ℂ 2 w))
    (hτ : ∀ g u, (τ g u : G → ℂ) =ᵐ[μ] fun x ↦ u (g⁻¹ * x))
    (hcτ : Continuous (fun z : G × Lp ℂ 2 w ↦ τ z.1 z.2))
    (φ : G → ℂ) (hφ : Integrable φ μ) (A : Lp ℂ 2 w →L[ℂ] Lp ℂ 2 w)
    (hA : ∀ u, HasPettisIntegral (.positive μ) (fun g ↦ φ g • τ g u) (A u))
    (u : Lp ℂ 2 w) :
    ∀ᵐ ψ ∂ν, ψ ∉ tsupport (lcaFourier μ φ) →
      (lcaFourier_unitary μ ν hν).exists.choose (J (A u)) ψ = 0 := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let U := (lcaFourier_unitary μ ν hν).exists.choose
  let S := tsupport (lcaFourier μ φ)
  have hclosed : IsClosed {u : Lp ℂ 2 w |
      ∀ᵐ ψ ∂ν, ψ ∉ S → U (J (A u)) ψ = 0} :=
    (spectralLineIsotype_bandProjections_support_closed ν S
      (isClosed_tsupport _).measurableSet).preimage
      (U.continuous.comp (J.continuous.comp A.continuous))
  have hD := spectralLineIsotype_bandProjections_dense_integrable μ w hle
  apply hclosed.closure_subset_iff.mpr ?_ (hD u)
  intro z hz
  let f := lcaConvolution μ φ z
  have hv : (J (A z) : G → ℂ) =ᵐ[μ] f :=
    pettis_convolution_haar_L2 μ J hJ τ hτ hcτ φ hφ z (A z) (hA z)
  have hf : MemLp f 2 μ := (Lp.memLp (J (A z))).ae_eq hv
  have heq : J (A z) = hf.toLp f := Lp.ext (hv.trans hf.coeFn_toLp.symm)
  have hFourier : (U (J (A z)) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f := by
    rw [heq]
    exact (lcaFourier_unitary μ ν hν).exists.choose_spec f
      (lcaConvolution_integrable μ hφ hz).2.1 hf
  filter_upwards [hFourier] with ψ hψ
  intro hψS
  rw [hψ, show lcaFourier μ f = _ from lcaFourier_convolution μ hφ hz,
    Pi.mul_apply, image_eq_zero_of_notMem_tsupport hψS, zero_mul]

private theorem spectralLineIsotype_bandProjections_zeroLine_support
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (s : ℝ) (hs : 0 ≤ s)
    (ν : Measure (PontryaginDual G)) (hν : IsLCAPlancherelMeasure μ ν) :
    let W := CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 0 0 s
    let A := (existsUnique_schwartzBruhat_zeroLineAction μ m s hs).exists.choose
    let U := (lcaFourier_unitary μ ν hν).exists.choose
    ∃ J : W →L[ℂ] Lp ℂ 2 μ,
      (∀ u, (J u : G → ℂ) =ᵐ[μ] (u : G → ℂ)) ∧
      ∀ (φ : SchwartzBruhat G) (u : W), ∀ᵐ ψ ∂ν,
        ψ ∉ tsupport (lcaFourier μ φ) → U (J (A φ u)) ψ = 0 := by
  intro W A U
  let w := μ.withDensity fun x ↦ ENNReal.ofReal
    (intervalSobolevDensity 0 0 s (Real.log ((m x).val : ℝ)))
  have hle : μ ≤ w := by
    calc
      μ = μ.withDensity 1 := withDensity_one.symm
      _ ≤ _ := withDensity_mono (.of_forall fun x ↦ by
        change 1 ≤ ENNReal.ofReal (intervalSobolevDensity 0 0 s _)
        rw [ENNReal.one_le_ofReal]
        simpa [intervalSobolevDensity] using Real.one_le_rpow
          (le_add_of_nonneg_right (sq_nonneg _)) (by linarith : 0 ≤ s / 2))
  let : IsLocallyFiniteMeasure w := IsLocallyFiniteMeasure.withDensity_ofReal
    ((continuous_intervalSobolevDensity 0 0 s).comp (continuous_logModule' m))
  obtain ⟨J, hJ⟩ := exists_L2_restriction w μ hle
  refine ⟨J, hJ, ?_⟩
  intro φ u
  exact spectralLineIsotype_bandProjections_convolution_support μ ν hν w hle J hJ
    (hardySobolevTranslation μ m 0 0 s le_rfl hs)
    (hardySobolevTranslation_apply μ m 0 0 s le_rfl hs)
    (exists_hardySobolevTranslation μ m 0 0 s le_rfl hs).choose_spec.2
    (φ : G → ℂ) ((schwartzBruhat_fourier_equiv μ).choose_spec φ).1 (A φ)
    ((existsUnique_schwartzBruhat_zeroLineAction μ m s hs).exists.choose_spec φ) u

/-- Paper: Remark 10.2.1.5, p. 444. The projections on the isotypic quotient
onto the closures of the images of the Fourier bands converge strongly to
the identity. Each orthogonal projection selects a closest element of its range.
Deviation: The Fourier bands use the inverse lift for left translation. -/
theorem spectralLineIsotype_bandProjections (χ : PontryaginDual C𝔽) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) (ν : Measure (PontryaginDual C𝔽)) (hν : IsLCAPlancherelMeasure μ𝔽 ν) :
    let hI : (0 : ℝ) ≤ 0 := le_rfl
    let ω := PontryaginDual.map restriction χ
    let E := Wω(hI, hs, ω)
    let N := (Θ(a, hI, hs)).comap E.subtype
    let Q := spectralSobolevIsotypeQuotient F a hI hs ω
    let U := (lcaFourier_unitary μ𝔽 ν hν).exists.choose
    let B (n : ℕ) := {q : Q | ∃ f : E,
      q = N.mkQ f ∧ ∃ u : Lp ℂ 2 μ𝔽, (u : C𝔽 → ℂ) =ᵐ[μ𝔽] (f.val : C𝔽 → ℂ) ∧
        ∀ᵐ ψ ∂ν, ψ ∉ modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n → U u ψ = 0}
    ∃ P : ℕ → (Q →L[ℂ] Q),
      (∀ n, range (P n) = closure (B n)) ∧
      (∀ n q y, y ∈ closure (B n) → ‖q - P n q‖ ≤ ‖q - y‖) ∧
      ∀ q, Tendsto (fun n ↦ P n q) atTop (𝓝 q) := by
  intro hI ω E N Q U B
  have hrestriction :=
    spectralLineIsotype_bandProjections_zeroLine_support (G := C𝔽) μ𝔽 m𝔽 s hs ν hν
  let J := hrestriction.choose
  have hJ := hrestriction.choose_spec.1
  have hJsupp := hrestriction.choose_spec.2
  have hconvolution := exists_spectralLineIsotypeConvolution (F := F) χ hs
  let φ := hconvolution.choose
  let R := hconvolution.choose_spec.choose
  have hband := hconvolution.choose_spec.choose_spec.2.2.1
  have hR := hconvolution.choose_spec.choose_spec.2.2.2.1
  have hlim := hconvolution.choose_spec.choose_spec.2.2.2.2
  have hsupported (n : ℕ) (f : E) :
      ∀ᵐ ψ ∂ν, ψ ∉ modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n →
        U (J (R n f).val) ψ = 0 := by
    have hsupp := hJsupp (φ n) f.val
    rw [hR n f]
    filter_upwards [hsupp] with ψ hψ
    intro hψband
    exact hψ (fun hψsupp ↦ hψband (hband n hψsupp))
  exact spectralLineIsotype_bandProjections_of_supported_approximants
    (X := C𝔽) (Y := PontryaginDual C𝔽) (E := E) (Q := Q)
    μ𝔽 ν (fun f : E ↦ (f.val : C𝔽 → ℂ))
    (J.toLinearMap.comp E.subtype) (fun f ↦ hJ f.val)
    (spectralSobolevIsotypeQuotient_mk a hI hs ω)
    (spectralSobolevIsotypeQuotient_mk_surjective a hI hs ω) U.toLinearEquiv.toLinearMap
    (fun n ↦ modulatedFrequencyBand m𝔽 χ⁻¹ (-(n : ℝ)) n)
    (fun n f ↦ R n f) hsupported hlim

end BandProjections

/-- Paper: (10.2.2.5)–(10.2.2.6), p. 446. Keep the full multiplicity in
the strip interior and apply the boundary cutoff at the two endpoints.
Deviation: Extend by zero off the strip and use the strict boundary cutoff. -/
def spectralStripMultiplicity (α s b : ℝ) (N : ℕ) : ℕ :=
  if -α < b ∧ b < α then N
  else if b = -α ∨ b = α then spectralBoundaryMultiplicity s N else 0

/-- Paper: (10.2.2.5), p. 446. At either boundary the strip multiplicity
is the truncated multiplicity. -/
theorem spectralStripMultiplicity_boundary {α b : ℝ} (_hα : 0 ≤ α)
    (_hb : b = -α ∨ b = α) (s : ℝ) (N : ℕ) :
    spectralStripMultiplicity α s b N = spectralBoundaryMultiplicity s N := by
  unfold spectralStripMultiplicity
  split_ifs with h1
  · exfalso
    rcases _hb with rfl | rfl <;> linarith [h1.1, h1.2]
  · rfl

/-- Paper: (10.2.2.6), p. 446. At an interior point every order below the
zero multiplicity is retained. -/
theorem spectralStripMultiplicity_interior {α b : ℝ} (_hb : b ∈ Ioo (-α) α) (s : ℝ) (N : ℕ) :
    spectralStripMultiplicity α s b N = N := by
  unfold spectralStripMultiplicity
  rw [mem_Ioo] at _hb
  simp [_hb]

/-- Paper: Theorem 10.2.2.1, p. 446. Index the strip jets by the norm-one
component, real offset, ordinate, and surviving derivative order. The point
of evaluation has real part a+b. -/
abbrev SpectralStripJetIndex (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a α s : ℝ) :=
  {j : PontryaginDual C₁ × ℝ × ℝ × ℕ //
    j.2.2.2 < spectralStripMultiplicity α s j.2.1
      (multiplicity(χ j.1, shift(a + j.2.1, j.2.2.1)))}

/-- Paper: Theorem 10.2.2.1, p. 446. Every strip jet is indexed by a
point in the closed strip and that point is a zero of the completed L-function. -/
theorem SpectralStripJetIndex.mem_strip_order_pos {χ : PontryaginDual C₁ → PontryaginDual C𝔽}
    {a α s : ℝ} (_hα : 0 ≤ α) (j : SpectralStripJetIndex χ a α s) :
    j.val.2.1 ∈ Icc (-α) α ∧
      0 < vanishingOrder(χ j.val.1, shift(a + j.val.2.1, j.val.2.2.1)) := by
  have key : ∀ o : WithTop ℤ, 0 < o.untop₀.toNat → 0 < o := by
    intro o h
    cases o with
    | top => simp at h
    | coe n =>
      rw [WithTop.untop₀_coe] at h
      exact_mod_cast (by omega : 0 < n)
  have h := j.2
  unfold spectralStripMultiplicity spectralBoundaryMultiplicity at h
  split_ifs at h with h1 h2
  · exact ⟨⟨h1.1.le, h1.2.le⟩, key _ (by omega)⟩
  · refine ⟨?_, key _ (by omega)⟩
    rw [mem_Icc]
    rcases h2 with h2 | h2 <;> constructor <;> linarith
  · omega

private theorem integrable_exp_neg_abs_mul_pow {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Integrable (fun x : ℝ ↦ Real.exp (-c * |x|) * x ^ (2 * k)) volume := by
  have hcont : Continuous (fun x : ℝ ↦ Real.exp (-c * |x|) * x ^ (2 * k)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul (continuous_id.pow (2 * k))
  let M : ℝ := ((2 * k).factorial : ℝ) / c ^ (2 * k) +
    ((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)
  have hdom : Integrable (fun x : ℝ ↦ M * (1 + x ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul M
  refine hdom.mono' hcont.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have hnonneg : 0 ≤ Real.exp (-c * |x|) * x ^ (2 * k) :=
    mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x)
  rw [Real.norm_of_nonneg hnonneg]
  have hu : 0 ≤ c * |x| := mul_nonneg hc.le (abs_nonneg x)
  have h1 : (c * |x|) ^ (2 * k) / ((2 * k).factorial : ℝ) ≤ Real.exp (c * |x|) :=
    Real.pow_div_factorial_le_exp (c * |x|) hu (2 * k)
  have h2 : (c * |x|) ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ) ≤ Real.exp (c * |x|) :=
    Real.pow_div_factorial_le_exp (c * |x|) hu (2 * k + 2)
  have hfac1 : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
  have hfac2 : (0 : ℝ) < ((2 * k + 2).factorial : ℝ) := by positivity
  have hc1 : 0 < c ^ (2 * k) := pow_pos hc _
  have hc2 : 0 < c ^ (2 * k + 2) := pow_pos hc _
  have hpow1 : x ^ (2 * k) ≤ (((2 * k).factorial : ℝ) / c ^ (2 * k)) * Real.exp (c * |x|) := by
    have hmul : (c * |x|) ^ (2 * k) ≤ ((2 * k).factorial : ℝ) * Real.exp (c * |x|) := by
      linarith [(div_le_iff₀ hfac1).mp h1]
    have hxa : |x| ^ (2 * k) = x ^ (2 * k) := by
      rw [pow_mul, sq_abs, ← pow_mul]
    rw [mul_pow, hxa] at hmul
    rw [div_mul_eq_mul_div, le_div_iff₀ hc1]
    linarith
  have hpow2 : x ^ (2 * k) * x ^ 2 ≤
      (((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)) * Real.exp (c * |x|) := by
    have hmul : (c * |x|) ^ (2 * k + 2) ≤ ((2 * k + 2).factorial : ℝ) * Real.exp (c * |x|) := by
      linarith [(div_le_iff₀ hfac2).mp h2]
    have hxa : |x| ^ (2 * k + 2) = x ^ (2 * k) * x ^ 2 := by
      rw [pow_add, pow_mul, sq_abs, ← pow_mul]
    rw [mul_pow, hxa] at hmul
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
    linarith
  have hsum : x ^ (2 * k) * (1 + x ^ 2) ≤ M * Real.exp (c * |x|) := by
    have : x ^ (2 * k) * (1 + x ^ 2) = x ^ (2 * k) + x ^ (2 * k) * x ^ 2 := by ring
    rw [this]
    have : M * Real.exp (c * |x|) =
        (((2 * k).factorial : ℝ) / c ^ (2 * k)) * Real.exp (c * |x|) +
        (((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)) * Real.exp (c * |x|) := by
      dsimp only [M]
      ring
    linarith
  have hexp_neg : Real.exp (-c * |x|) = (Real.exp (c * |x|))⁻¹ := by
    rw [neg_mul, Real.exp_neg]
  rw [hexp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _), mul_comm (M * _), ← mul_assoc]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + x ^ 2)]
  linarith

private theorem stripJet_integrand_continuous (α s b : ℝ) (k : ℕ) :
    Continuous (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
  ((Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).sub (continuous_const.mul continuous_abs))).mul
    (continuous_id.pow (2 * k))).mul
    (((continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
        Or.inl (by change (1 : ℝ) + x ^ 2 ≠ 0; positivity)).inv₀ fun x ↦
      (Real.rpow_pos_of_pos (by change (0 : ℝ) < 1 + x ^ 2; positivity) _).ne')

private theorem stripJet_integrand_eq {α : ℝ} (hα : 0 ≤ α) (s b : ℝ) (k : ℕ) (x : ℝ) :
    Real.exp (2 * b * x) * x ^ (2 * k) * (intervalSobolevDensity (-α) α s x)⁻¹ =
      Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
  rw [symmIntervalSobolevDensity_eq hα, mul_inv, Real.exp_sub, div_eq_mul_inv]
  ring

private theorem spectralStripJet_integrable {α s b : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {k : ℕ}
    (h : (-α < b ∧ b < α) ∨ ((b = -α ∨ b = α) ∧ 2 * (k : ℝ) + 1 < s)) :
    Integrable (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := by
  rcases h with ⟨hb1, hb2⟩ | ⟨hb, hk⟩
  · have hδ : 0 < α - |b| := by
      have : |b| < α := abs_lt.mpr ⟨hb1, hb2⟩
      linarith
    refine (integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * (α - |b|)) k).mono'
      (stripJet_integrand_continuous α s b k).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    have hnonneg : 0 ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    rw [Real.norm_of_nonneg hnonneg]
    have hbx : b * x ≤ |b| * |x| := by
      calc
        b * x ≤ |b * x| := le_abs_self _
        _ = |b| * |x| := abs_mul b x
    have hexp : Real.exp (2 * b * x - 2 * α * |x|) ≤ Real.exp (-(2 * (α - |b|)) * |x|) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hinv_le : ((1 + x ^ 2) ^ (s / 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith))
    calc
      Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹
        ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) * 1 :=
          mul_le_mul_of_nonneg_left hinv_le
            (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
      _ = Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) := mul_one _
      _ ≤ Real.exp (-(2 * (α - |b|)) * |x|) * x ^ (2 * k) :=
          mul_le_mul_of_nonneg_right hexp (Even.pow_nonneg (even_two_mul k) x)
  · refine (integrable_pow_mul_rpow_inv hk).mono'
      (stripJet_integrand_continuous α s b k).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    have hnonneg : 0 ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    rw [Real.norm_of_nonneg hnonneg, mul_assoc]
    have hba : |b| = α := by
      rcases hb with rfl | rfl
      · rw [abs_neg, abs_of_nonneg hα]
      · exact abs_of_nonneg hα
    have hbx : b * x ≤ α * |x| := by
      calc
        b * x ≤ |b * x| := le_abs_self _
        _ = |b| * |x| := abs_mul b x
        _ = α * |x| := by rw [hba]
    have hexp : Real.exp (2 * b * x - 2 * α * |x|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    calc
      Real.exp (2 * b * x - 2 * α * |x|) * (x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹)
        ≤ 1 * (x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
          mul_le_mul_of_nonneg_right hexp
            (mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
              (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le))
      _ = x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := one_mul _

/-- Paper: Theorem 10.2.2.1, p. 446. The admitted strip jets are
square-integrable for the reciprocal strip weight.
Deviation: Exclude the divergent boundary endpoint of (10.2.2.5). -/
theorem spectralStripJet_memLp (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (_hα : 0 ≤ α) (_hs : 0 ≤ s) (j : SpectralStripJetIndex χ a α s) :
    MemLp (stripJet(χ, j)) 2 (L2μ'(-α, α, s)) := by
  have hcond : (-α < j.val.2.1 ∧ j.val.2.1 < α) ∨
      ((j.val.2.1 = -α ∨ j.val.2.1 = α) ∧ 2 * (j.val.2.2.2 : ℝ) + 1 < s) := by
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with h1 h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2, ?_⟩
      have horder : (j.val.2.2.2 : ℝ) < (s - 1) / 2 :=
        ((lt_spectralBoundaryMultiplicity s _ _).mp hj).2
      linarith
    · omega
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hν : Integrable (fun g : C𝔽 ↦
      Real.exp (2 * j.val.2.1 * logNorm g - 2 * α * |logNorm g|) *
        (logNorm g) ^ (2 * j.val.2.2.2) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹) ν :=
    (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽).integrable_comp_of_integrable
      (spectralStripJet_integrable _hα _hs hcond)
  have hμ : Integrable (fun g : C𝔽 ↦
      Real.exp (2 * j.val.2.1 * logNorm g - 2 * α * |logNorm g|) *
        (logNorm g) ^ (2 * j.val.2.2.2) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹) μ𝔽 := by
    rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    exact hν.smul_measure_nnreal
  apply (memLp_two_iff_integrable_sq_norm
    (spectralZeroJet_continuous (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2).aestronglyMeasurable).2
  apply (integrable_withDensity_iff
    ((symmIntervalSobolevDensity_inv_continuous _hα s).measurable.ennreal_ofReal)
    (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)).2
  refine hμ.congr (ae_of_all μ𝔽 fun g ↦ ?_)
  dsimp only
  rw [spectralZeroJet_norm_sq,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (symmIntervalSobolevDensity_pos _hα s (logNorm g)).le),
    stripJet_integrand_eq _hα]

section

open Polynomial
open scoped Polynomial

/-- Multiplying distinct powers of an additive coordinate by one character preserves
linear independence when the coordinate has infinite range. -/
private theorem jetPowers_independent {G : Type*} [Group G] (χ : G →* ℂ)
    (L : G → ℂ) (hL : (range L).Infinite) :
    LinearIndependent ℂ (fun n : ℕ ↦ fun g ↦ χ g * (L g) ^ n) := by
  let E : ℂ[X] →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun p g ↦ χ g * p.eval (L g)
      map_add' := fun p q ↦ funext fun g ↦ by simp [mul_add]
      map_smul' := fun r p ↦ funext fun g ↦ by simp [smul_eq_mul, mul_left_comm] }
  have einj : Injective E := by
    intro p q h
    apply Polynomial.eq_of_infinite_eval_eq
    refine hL.mono ?_
    rintro _ ⟨g, rfl⟩
    exact mul_left_cancel₀ ((Group.isUnit g).map χ).ne_zero (congrFun h g)
  have h := (Polynomial.basisMonomials ℂ).linearIndependent.map' E (LinearMap.ker_eq_bot.mpr einj)
  simpa only [Function.comp_def, Polynomial.coe_basisMonomials, E, LinearMap.coe_mk, AddHom.coe_mk,
    Polynomial.eval_monomial, one_mul] using h

/-- Translations put the character times the mth power of an additive coordinate in
the simultaneous generalized eigenspace of that character. -/
private theorem jetPowers_mem_weight {G : Type*} [CommGroup G] (χ : G →* ℂ) (L : G → ℂ)
    (hL : ∀ g y, L (g * y) = L g + L y)
    (τ : G → Module.End ℂ (G → ℂ)) (hτ : ∀ g f y, τ g f y = f (g * y)) (m : ℕ) :
    (fun g ↦ χ g * (L g) ^ m) ∈ ⨅ g, (τ g).maxGenEigenspace (χ g) := by
  apply (Submodule.mem_iInf _).mpr
  intro g
  let v (i : ℕ) (y : G) := χ y * (L y) ^ i
  let δ := τ g - χ g • (1 : Module.End ℂ (G → ℂ))
  change v m ∈ (τ g).maxGenEigenspace (χ g)
  induction m using Nat.strong_induction_on with | ind m ih => ?_
  let c (i : ℕ) := χ g * (L g) ^ (m - i) * (m.choose i : ℂ)
  have diff : δ (v m) = ∑ i ∈ Finset.range m, c i • v i := by
    funext y
    change τ g (v m) y - χ g * v m y = _
    rw [hτ]
    have hsum : v m (g * y) = ∑ i ∈ Finset.range (m+1), c i * v i y := by
      simp only [v, map_mul, hL]
      rw [add_comm (L g), add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      dsimp only [c]
      ring
    rw [hsum, Finset.sum_range_succ]
    simp [c, Finset.sum_apply]
  have hmem : δ (v m) ∈ (τ g).maxGenEigenspace (χ g) := by
    rw [diff]
    exact Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ (ih i (Finset.mem_range.mp hi))
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hmem
  apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
  exact ⟨k+1, by simpa only [pow_succ, mul_apply_eq_comp] using hk⟩

/-- Exponential polynomials attached to distinct characters have independent coefficients. -/
private theorem jetPowers_all_independent {G Z : Type*} [CommGroup G]
    (χ : Z → G →* ℂ) (hc : Injective χ) (L : G → ℂ)
    (hL : ∀ g y, L (g * y) = L g + L y) (hi : (range L).Infinite) :
    LinearIndependent ℂ (fun zn : (_ : Z) × ℕ ↦ fun g ↦ χ zn.1 g * (L g) ^ zn.2) := by
  let τ (g : G) : Module.End ℂ (G → ℂ) :=
    { toFun := fun f y ↦ f (g * y), map_add' := by intros; rfl, map_smul' := by intros; rfl }
  have ht (g f y) : τ g f y = f (g * y) := rfl
  have hcomm (a b : G) : Commute (τ a) (τ b) := by
    apply LinearMap.ext
    intro f
    funext y
    change f (b * (a * y)) = f (a * (b * y))
    rw [mul_left_comm]
  have hind : iSupIndep (fun ψ : G → ℂ ↦ ⨅ g, (τ g).maxGenEigenspace (ψ g)) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo τ
    (fun i j p ↦ Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) p)
  let V (z : Z) (n : ℕ) := fun g ↦ χ z g * (L g) ^ n
  have hiχ : Injective (fun z g ↦ χ z g) := fun _ _ h ↦ hc (MonoidHom.ext (congrFun h))
  have hspaces : iSupIndep fun z ↦ Submodule.span ℂ (range (V z)) :=
    (hind.comp hiχ).mono (by
      intro z
      apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact jetPowers_mem_weight (χ z) L hL τ ht n)
  apply linearIndependent_iUnion_finite (f := V) (fun z ↦ jetPowers_independent (χ z) L hi)
  exact fun _ _ _ hz ↦ hspaces.disjoint_biSup hz

section StripJetIndependence

private theorem spectralStripJet_twist_injective
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) :
    Injective (fun p : PontryaginDual C₁ × ℂ ↦ (ideleClassNormTwist (χ p.1) p.2).toMonoidHom) := by
  have hres (ω : PontryaginDual C₁) (z : ℂ) (g : C₁) :
      ideleClassNormTwist (χ ω) z g.val = (ω g : ℂ) := by
    change (χ ω g.val : ℂ) * ((((ideleClassNorm F g.val).val : ℝ) : ℂ) ^ z) = _
    rw [show ideleClassNorm F g.val = 1 from g.property]
    simp only [Units.val_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one]
    exact congrArg ((↑) : Circle → ℂ) (DFunLike.congr_fun (hχ ω) g)
  rintro ⟨ω, z⟩ ⟨η, w⟩ he
  have htw : ideleClassNormTwist (χ ω) z = ideleClassNormTwist (χ η) w :=
    ContinuousMonoidHom.ext fun g ↦ DFunLike.congr_fun he g
  have hω : ω = η := by
    ext g : 1
    apply Subtype.ext
    exact (hres ω z g).symm.trans ((DFunLike.congr_fun htw g.val).trans (hres η w g))
  subst η
  have hu := hχ.existsUnique_normTwist ω (ideleClassNormTwist (χ ω) z) (hres ω z)
  exact Prod.ext rfl (hu.unique rfl htw)

/-- Distinct choices of base character, both real coordinates of a norm twist, or
logarithmic degree give linearly independent functions on the idele class group. -/
private theorem spectralAdelicJet_linearIndependent
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) :
    LinearIndependent ℂ (fun j : PontryaginDual C₁ × ℝ × ℝ × ℕ ↦
      spectralZeroJet (χ j.1) j.2.1 j.2.2.1 j.2.2.2) := by
  let L (g : C𝔽) : ℂ := logNorm g
  have hadd (g y : C𝔽) : L (g * y) = L g + L y := by
    dsimp only [L, logIdeleClassNorm]
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero)
      (NNReal.coe_ne_zero.2 (ideleClassNorm F y).ne_zero), Complex.ofReal_add]
  have hinf : (range L).Infinite := by
    refine (Set.infinite_range_of_injective Complex.ofReal_injective).mono ?_
    rintro _ ⟨r, rfl⟩
    let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    let g : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F (e r))
    have hg : ideleClassNorm F g = e r := canonicalIdeleNormSection_rightInverse F _
    refine ⟨g, ?_⟩
    change (Real.log ((ideleClassNorm F g).val : ℝ) : ℂ) = r
    rw [hg]
    exact congrArg ((↑) : ℝ → ℂ) (Real.log_exp r)
  let char (p : PontryaginDual C₁ × ℂ) := (ideleClassNormTwist (χ p.1) p.2).toMonoidHom
  let key (j : PontryaginDual C₁ × ℝ × ℝ × ℕ) : (_ : PontryaginDual C₁ × ℂ) × ℕ :=
    ⟨(j.1, shift(j.2.1, j.2.2.1)), j.2.2.2⟩
  have hk : Injective key := by
    intro i j he
    have hω := congrArg (fun p ↦ p.1.1) he
    have hre := congrArg (fun p ↦ p.1.2.re) he
    have him := congrArg (fun p ↦ p.1.2.im) he
    have hn : i.2.2.2 = j.2.2.2 := eq_of_heq (Sigma.mk.inj he).2
    exact Prod.ext hω (Prod.ext (by simpa [key] using hre) (Prod.ext (by simpa [key] using him) hn))
  exact (jetPowers_all_independent char (spectralStripJet_twist_injective χ hχ) L hadd hinf).comp key hk

private theorem spectralStripJet_raw_linearIndependent
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (a α s : ℝ) :
    LinearIndependent ℂ (fun j : SpectralStripJetIndex χ a α s ↦
      spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2) :=
  (spectralAdelicJet_linearIndependent χ hχ).comp Subtype.val Subtype.val_injective

open Filter MeasureTheory

/-- Continuous representatives remain linearly independent in L² when a measure positive
on open sets is absolutely continuous with respect to the L² measure. -/
private theorem jetFunctions_toLp_independent {X I : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (μ ν : Measure X) [μ.IsOpenPosMeasure] (hμ : μ ≪ ν)
    (f : I → X → ℂ) (hc : ∀ i, Continuous (f i)) (hm : ∀ i, MemLp (f i) 2 ν)
    (hi : LinearIndependent ℂ f) :
    LinearIndependent ℂ (fun i ↦ (hm i).toLp (f i)) := by
  rw [linearIndependent_iff'] at hi ⊢
  intro t c hz
  apply hi t c
  have he (i : I) : ((c i • (hm i).toLp (f i) : Lp ℂ 2 ν) : X → ℂ) =ᵐ[ν] c i • f i :=
    (Lp.coeFn_smul _ _).trans ((hm i).coeFn_toLp.const_smul _)
  have hsum : (⇑(∑ i ∈ t, c i • (hm i).toLp (f i)) : X → ℂ) =ᵐ[ν] ∑ i ∈ t, c i • f i :=
    (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum fun i _ ↦ he i)
  rw [hz] at hsum
  apply MeasureTheory.Measure.eq_of_ae_eq (hμ.ae_le (hsum.symm.trans (Lp.coeFn_zero _ _ _)))
  · have hfun : (∑ i ∈ t, c i • f i) = fun x ↦ ∑ i ∈ t, (c i • f i) x := by
      funext x
      exact Finset.sum_apply _ _ _
    rw [hfun]
    exact continuous_finsetSum t fun i _ ↦ (hc i).const_smul (c i)
  · exact continuous_zero

/-- Paper: Theorem 10.2.2.1, p. 446. The surviving strip jets form a linearly
independent family in reciprocal-weight L². This holds already for finite
linear combinations, before passing to any quotient or choosing interpolants. -/
theorem spectralStripJet_toLp_linearIndependent
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    LinearIndependent ℂ (fun j : SpectralStripJetIndex χ a α s ↦
      (spectralStripJet_memLp χ hα hs j).toLp (spectralZeroJet
        (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) := by
  let μ := ideleClassTamagawaMeasure F
  let w (g : C𝔽) := intervalSobolevDensity (-α) α s (logNorm g)
  let ν := μ.withDensity (fun g ↦ ENNReal.ofReal (w g)⁻¹)
  have hw : Measurable w := by
    have hD : Continuous (intervalSobolevDensity (-α) α s) := by
      unfold intervalSobolevDensity
      fun_prop
    exact hD.measurable.comp ((NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).measurable.log)
  have habs : μ ≪ ν := by
    refine withDensity_absolutelyContinuous' hw.inv.ennreal_ofReal.aemeasurable (.of_forall fun g ↦ ?_)
    refine ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ?_)
    exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hlog : Continuous logNorm := (NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).log
      (fun g ↦ NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero)
  apply jetFunctions_toLp_independent μ ν habs _ (fun j ↦ ?_) _
    (spectralStripJet_raw_linearIndependent χ hχ a α s)
  exact (ideleClassNormTwist (χ j.val.1) (shift(j.val.2.1, j.val.2.2.1))).continuous.mul
    ((Complex.continuous_ofReal.comp hlog).pow _)

end StripJetIndependence

end

local notation "stripI(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripU(" χ ", " hα ", " hs ")" =>
  (fun j ↦ (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j)))

section StripThetaAnnihilation

local notation "ℬ" => SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))

/-- Factorization on a right half-plane determines the equality of meromorphic
orders everywhere. -/
private theorem stripTheta_order_of_factor {Z L A : ℂ → ℂ} (hZ : Differentiable ℂ Z)
    (hL : MeromorphicOn L univ) (hA : AnalyticOnNhd ℂ A univ)
    (heq : ∀ z : ℂ, 1 < z.re → Z z = L z * A z) (w : ℂ) :
    meromorphicOrderAt Z w = meromorphicOrderAt L w + meromorphicOrderAt A w := by
  have hLA : MeromorphicOn (L * A) univ := hL.mul (fun z hz ↦ (hA z hz).meromorphicAt)
  have hzM : MeromorphicOn Z univ := fun z _ ↦ (hZ.analyticAt z).meromorphicAt
  have hd : MeromorphicOn (Z - L * A) univ := hzM.sub hLA
  have ho : meromorphicOrderAt (Z - L * A) 2 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hnear : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with z hz using sub_eq_zero.mpr (heq z hz)
  have hw := hd.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ w) ho
  have he : Z =ᶠ[𝓝[≠] w] L * A :=
    (meromorphicOrderAt_eq_top_iff.mp hw).mono fun z hz ↦ sub_eq_zero.mp hz
  rw [meromorphicOrderAt_congr he, meromorphicOrderAt_mul (hL w (mem_univ w)) (hA w (mem_univ w)).meromorphicAt]

private theorem stripTheta_deriv_of_order {Z L : ℂ → ℂ} {w : ℂ} (hZ : AnalyticAt ℂ Z w)
    (ho : meromorphicOrderAt L w ≤ meromorphicOrderAt Z w) {k : ℕ}
    (hk : k < (meromorphicOrderAt L w).untop₀.toNat) : iteratedDeriv k Z w = 0 := by
  have hlt : (k : WithTop ℤ) < meromorphicOrderAt L w := by
    cases h : meromorphicOrderAt L w with
    | top => simp
    | coe n =>
      rw [h, WithTop.untop₀_coe] at hk
      exact WithTop.coe_lt_coe.mpr (by omega)
  have hl := hlt.trans_le ho
  rw [hZ.meromorphicOrderAt_eq] at hl
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := k+1) hZ).mp _ k (Nat.lt_succ_self k)
  cases h : analyticOrderAt Z w with
  | top => simp
  | coe n =>
    rw [h, ENat.map_natCast] at hl
    exact WithTop.coe_le_coe.mpr (by exact_mod_cast (show (k : ℤ) < n from WithTop.coe_lt_coe.mp hl))

/-- The normalized eigendistribution is the entire test factor and the two
orders add at every point. -/
private theorem stripTheta_mellin_factor_order (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F) (w : ℂ) :
    let Z := fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
    let L := continuedCompletedHeckeL χ
    let Φ := fun z ↦ (adelicEigendistribution_normalized χ).choose z f.val
    AnalyticAt ℂ Φ w ∧ meromorphicOrderAt Z w = meromorphicOrderAt L w + meromorphicOrderAt Φ w := by
  let Z (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
  let L := continuedCompletedHeckeL χ
  obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hZ : Differentiable ℂ Z := globalThetaMellinIntegral_entire_of_vanishing f.val hf hf' χ
  let D := (adelicEigendistribution_normalized χ).choose
  have hD := (adelicEigendistribution_normalized χ).choose_spec
  let d : ℂ := ((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ)
  let A (z : ℂ) := d * D z f.val
  have hE : AnalyticOnNhd ℂ (fun z ↦ D z f.val) univ := by
    let e : StrongDual ℂ ℬ →L[ℂ] ℂ := ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) f.val
    have hE : Differentiable ℂ (e ∘ D) := by
      intro z
      have hd := hD.1.hasFDerivAt (isOpen_univ.mem_nhds (mem_univ z))
      have he : HasFDerivAt (e ∘ D) (e.comp (fderiv ℂ D z)) z := by
        apply HasFDerivAt.of_isLittleOTVS
        simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
          using e.isBigOTVS_comp.trans_isLittleOTVS hd.isLittleOTVS
      exact he.differentiableAt
    exact fun z _ ↦ hE.analyticAt z
  have hA : AnalyticOnNhd ℂ A univ := analyticOnNhd_const.mul hE
  have hσ (ψ : PontryaginDual C𝔽) (z : ℂ) := quasiCharacterAbscissa_of_unitary_twist
    (ideleClassNorm F) (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F))
    (ideleClassNormTwist ψ z) ψ z (fun _ ↦ rfl)
  have hfact (z : ℂ) (hz : 1 < z.re) : Z z = L z * A z := by
    let σ := quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F))
    have h0 : σ 1 = 0 := by
      change Real.log ‖(1 : ℂ)‖ / _ = 0
      rw [norm_one, Real.log_one, zero_div]
    have hn : ideleClassNormTwist χ z ≠ 1 := fun h ↦ (zero_lt_one.trans hz).ne'
      ((hσ χ z).symm.trans ((congrArg σ h).trans h0))
    have hn' : ideleClassNormTwist χ z ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1 :=
      fun h ↦ hz.ne' ((hσ χ z).symm.trans ((congrArg σ h).trans (hσ _ 1)))
    have hzeta := congrFun (globalThetaMellinIntegral_eq_continuation_of_vanishing f.val hf hf')
      (ideleClassNormTwist χ z)
    refine hzeta.trans ((hD.2.2 z hn hn' f.val).trans ?_)
    rw [gaussianCompletedHeckeL_eq_completedHeckeL χ z hz]
    have h := (continuedCompletedHeckeL_spec χ).2 ⟨z,hz⟩
    change d * completedHeckeL χ ⟨z,hz⟩ * D z f.val = L z * (d * D z f.val)
    rw [← h]
    ring
  have he := stripTheta_order_of_factor hZ (continuedCompletedHeckeL_spec χ).1.meromorphicOn hA hfact w
  have hd : d ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr
    (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F))).ne')
  have ha : meromorphicOrderAt A w = meromorphicOrderAt (fun z ↦ D z f.val) w :=
    meromorphicOrderAt_mul_of_ne_zero (g := fun _ ↦ d) analyticAt_const hd
  exact ⟨hE w (mem_univ w), he.trans (congrArg (meromorphicOrderAt L w + ·) ha)⟩

/-- The completed L-function divides each polar-free theta Mellin transform as
a germ; equality of orders holds wherever the normalized eigendistribution is nonzero. -/
private theorem stripTheta_mellin_order (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F) (w : ℂ) :
    let Z := fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
    let L := continuedCompletedHeckeL χ
    meromorphicOrderAt L w ≤ meromorphicOrderAt Z w ∧
      ((adelicEigendistribution_normalized χ).choose w f.val ≠ 0 →
        meromorphicOrderAt Z w = meromorphicOrderAt L w) := by
  obtain ⟨hA, he⟩ := stripTheta_mellin_factor_order χ f w
  refine ⟨(le_add_of_nonneg_right hA.meromorphicOrderAt_nonneg).trans he.symm.le, fun hu ↦ ?_⟩
  exact he.trans (by rw [hA.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hu, add_zero])

/-- The Mellin derivatives below the completed L-function’s order vanish. -/
private theorem stripTheta_mellin_zero (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F)
    (w : ℂ) (k : ℕ) (hk : k < (meromorphicOrderAt (continuedCompletedHeckeL χ) w).untop₀.toNat) :
    iteratedDeriv k (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) w = 0 := by
  obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  exact stripTheta_deriv_of_order (globalThetaMellinIntegral_entire_of_vanishing f.val hf hf' χ |>.analyticAt w)
    (stripTheta_mellin_order χ f w).1 hk

/-- Two translation differences kill the polar coordinates while preserving a
nonzero eigenfunctional of any distinct weight. -/
private theorem polarShift_preserve {E G : Type*} [AddCommGroup E] [Module ℂ E]
    (P : E →ₗ[ℂ] ℂ × ℂ) (D : E →ₗ[ℂ] ℂ) (τ : G → E → E) (c₀ c₁ c : G → ℂ)
    (hp₀ : ∀ g f, (P (τ g f)).1 = c₀ g * (P f).1)
    (hp₁ : ∀ g f, (P (τ g f)).2 = c₁ g * (P f).2)
    (hd : ∀ g f, D (τ g f) = c g * D f) (f : E) (hf : D f ≠ 0)
    {g h : G} (hg : c g ≠ c₀ g) (hh : c h ≠ c₁ h) : ∃ f' : P.ker, D f'.val ≠ 0 := by
  let x := τ g f - c₀ g • f
  let y := τ h x - c₁ h • x
  have h₀ : (P x).1 = 0 := by simp [x, hp₀]
  have hP : P y = 0 := by
    ext <;> simp [y, hp₀, hp₁, h₀]
  refine ⟨⟨y, hP⟩, ?_⟩
  have hval : D y = (c h - c₁ h) * (c g - c₀ g) * D f := by
    simp [y, x, hd]
    ring
  exact hval ▸ mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hh) (sub_ne_zero.mpr hg)) hf

private theorem stripTheta_normalized_nonzero_on_polar (χ : PontryaginDual C𝔽) (w : ℂ)
    (h₀ : ideleClassNormTwist χ w ≠ 1)
    (h₁ : ideleClassNormTwist χ w ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) :
    ∃ f : adelePolarSubspace F, (adelicEigendistribution_normalized χ).choose w f.val ≠ 0 := by
  classical
  let c := ideleClassNormTwist χ w
  let n := ideleClassNormTwist (1 : PontryaginDual C𝔽) 1
  let D := (adelicEigendistribution_normalized χ).choose w
  have hD := ((adelicEigendistribution_normalized χ).choose_spec.2.1 w D).mp rfl
  let π : IdeleGroup (𝓞 F) F → C𝔽 := QuotientGroup.mk
  have hsep (d : QuasiCharacter C𝔽) (hne : c ≠ d) : ∃ g, c (π g) ≠ d (π g) := by
    by_contra! hall
    apply hne
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact hall g
  obtain ⟨g,hg⟩ := hsep 1 h₀
  obtain ⟨h,hh⟩ := hsep n h₁
  let P := adelePolarValues (F := F)
  let τ := schwartzBruhatUnitTranslate (R := AdeleRing (𝓞 F) F)
  let K := (adelicThetaLinearMap F).ker
  have hact := (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2
  have hp₀ (g : IdeleGroup (𝓞 F) F) (f : ℬ) : (P (τ g f)).1 = (1 : QuasiCharacter C𝔽) (π g) * (P f).1 := by
    change (τ g f) (Multiplicative.ofAdd 0) = 1 * f (Multiplicative.ofAdd 0)
    rw [schwartzBruhatUnitTranslate_apply, mul_zero, one_mul]
  have hp₁ (g : IdeleGroup (𝓞 F) F) (f : ℬ) : (P (τ g f)).2 = n (π g) * (P f).2 := by
    have hh := globalThetaPolarValues_snd_translate (π g) (K.mkQL f)
    have hraw : (P (τ g f)).2 = ((ideleClassNorm F (π g)).val : ℝ) * (P f).2 :=
      (congrArg (fun x ↦ (globalThetaPolarValues (F := F) x).2) (hact g f).symm).trans hh
    change _ = ((1 : ℂ) * ((((ideleClassNorm F (π g)).val : ℝ) : ℂ) ^ (1 : ℂ))) * _
    simpa only [Complex.cpow_one, one_mul] using hraw
  exact polarShift_preserve P D.toLinearMap τ _ _ _ hp₀ hp₁ hD.1 (adelicStandardGaussian χ)
    (hD.2.trans_ne one_ne_zero) hg hh

/-- Paper: Theorem 3.4.3.3(2), p. 153, and Theorem 10.2.1.1, pp. 441–442.
At each twist away from the trivial character and the idelic norm, one polar-free
test attains the order of the completed Hecke L-function in its Mellin transform. -/
private theorem exists_globalThetaMellinIntegral_order_eq_of_regular (χ : PontryaginDual C𝔽) (w : ℂ)
    (h₀ : ideleClassNormTwist χ w ≠ 1)
    (h₁ : ideleClassNormTwist χ w ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) :
    ∃ f : adelePolarSubspace F,
      meromorphicOrderAt (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) w =
        meromorphicOrderAt (continuedCompletedHeckeL χ) w := by
  obtain ⟨f, hf⟩ := stripTheta_normalized_nonzero_on_polar χ w h₀ h₁
  exact ⟨f, (stripTheta_mellin_order χ f w).2 hf⟩

/-- Paper: Proposition 3.2.1.3(2), p. 123. In a unitary chart the trivial
quasi-character and the idelic norm correspond to simple poles of the completed L-function. -/
private theorem continuedCompletedHeckeL_order_of_exceptional (χ : PontryaginDual C𝔽) (w : ℂ)
    (he : ideleClassNormTwist χ w = 1 ∨
      ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) w = -1 := by
  have h0 : ideleClassNormTwist (1 : PontryaginDual C𝔽) 0 = 1 := by
    ext1 g
    change 1 * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (0 : ℂ)) = 1
    simp
  obtain ⟨z, hz, hc⟩ : ∃ z : ℂ, (z = 0 ∨ z = 1) ∧ ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) z := by
    rcases he with he | he
    · exact ⟨0, Or.inl rfl, he.trans h0.symm⟩
    · exact ⟨1, Or.inr rfl, he⟩
  have hres : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext g : 1
    apply Subtype.ext
    have hu := DFunLike.congr_fun hc g.val
    change (χ g.val : ℂ) * ((((ideleClassNorm F g.val).val : ℝ) : ℂ) ^ w) =
      1 * ((((ideleClassNorm F g.val).val : ℝ) : ℂ) ^ z) at hu
    rw [g.property] at hu
    change (χ g.val : ℂ) = 1
    simpa only [Units.val_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one] using hu
  obtain ⟨t, ⟨ht, hp₀, hp₁, _⟩, _⟩ := completedHeckeL_continuation_simplePoles χ _
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2 hres
  have heq : ideleClassNormTwist (1 : PontryaginDual C𝔽) (-Complex.I * (t : ℂ) + w) =
      ideleClassNormTwist (1 : PontryaginDual C𝔽) z := by
    simpa only [zero_add] using (ideleClassNormTwist_add_of_eq ht w).symm.trans (by simpa only [zero_add] using hc)
  let γ := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 z
  have hγ (u : ℝ≥0ˣ) : γ u = ((u.val : ℝ) : ℂ) ^ z := one_mul _
  have hc' : z = -Complex.I * (t : ℂ) + w := by
    apply (existsUnique_complexPower γ).unique hγ
    intro u
    let g : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F u)
    have hg : ideleClassNorm F g = u := canonicalIdeleNormSection_rightInverse F u
    have hu := DFunLike.congr_fun heq g
    change 1 * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ) + w)) = 1 * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ z) at hu
    rw [hg, one_mul, one_mul] at hu
    exact (hγ u).trans hu.symm
  rcases hz with rfl | rfl
  · exact (congrArg (meromorphicOrderAt (continuedCompletedHeckeL χ)) (by linear_combination -hc' : w = Complex.I * t)).trans hp₀
  · exact (congrArg (meromorphicOrderAt (continuedCompletedHeckeL χ)) (by linear_combination -hc' : w = 1 + Complex.I * t)).trans hp₁

/-- Paper: Theorem 10.2.1.1, pp. 441–442, and Theorem 10.2.2.1, p. 446.
At every zero of the completed Hecke L-function, some polar-free theta test has
a Mellin transform with exactly its multiplicity. -/
private theorem exists_globalThetaMellinIntegral_order_eq_of_zero (χ : PontryaginDual C𝔽) (w : ℂ)
    (hw : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) w) :
    ∃ f : adelePolarSubspace F,
      meromorphicOrderAt (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) w =
        meromorphicOrderAt (continuedCompletedHeckeL χ) w := by
  have hn : ¬ (ideleClassNormTwist χ w = 1 ∨
      ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) := by
    intro h
    rw [continuedCompletedHeckeL_order_of_exceptional χ w h] at hw
    exact (by decide : ¬ (0 : WithTop ℤ) < -1) hw
  exact exists_globalThetaMellinIntegral_order_eq_of_regular χ w (not_or.mp hn).1 (not_or.mp hn).2

/-- Paper: Theorem 10.2.2.1, p. 446, and (3.4.3.15), p. 153. On a polar-free test
the first nonvanishing Mellin derivative can attain the full Hecke multiplicity at
each admitted strip jet.
Deviation: This statement concerns derivatives of the test function's Mellin transform.
Only orders below the strict cutoff give continuous Sobolev moments at the boundary. -/
theorem SpectralStripJetIndex.exists_thetaMellin_first_nonvanishing
    {χ : PontryaginDual C₁ → PontryaginDual C𝔽} {a α s : ℝ} (j : SpectralStripJetIndex χ a α s) :
    let w := shift(a + j.val.2.1, j.val.2.2.1)
    let n := (meromorphicOrderAt (continuedCompletedHeckeL (χ j.val.1)) w).untop₀.toNat
    ∃ f : adelePolarSubspace F,
      let Z := fun u ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist (χ j.val.1) u)
      (∀ k < n, iteratedDeriv k Z w = 0) ∧ iteratedDeriv n Z w ≠ 0 := by
  intro w n
  let L := continuedCompletedHeckeL (χ j.val.1)
  have hn : 0 < n := by
    have h : j.val.2.2.2 < spectralStripMultiplicity α s j.val.2.1 n := j.property
    unfold spectralStripMultiplicity spectralBoundaryMultiplicity at h
    split_ifs at h <;> omega
  have hn' : 0 < meromorphicOrderAt L w ∧ meromorphicOrderAt L w = (n : WithTop ℤ) := by
    change 0 < (meromorphicOrderAt L w).untop₀.toNat at hn
    change 0 < meromorphicOrderAt L w ∧ meromorphicOrderAt L w = ((meromorphicOrderAt L w).untop₀.toNat : WithTop ℤ)
    cases h : meromorphicOrderAt L w with
    | top => simp [h] at hn
    | coe z =>
      rw [h, WithTop.untop₀_coe] at hn
      rw [WithTop.untop₀_coe]
      exact ⟨WithTop.coe_lt_coe.mpr (by omega), WithTop.coe_eq_coe.mpr (by omega)⟩
  obtain ⟨f, hf⟩ := exists_globalThetaMellinIntegral_order_eq_of_zero (χ j.val.1) w hn'.1
  let Z := fun u ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist (χ j.val.1) u)
  obtain ⟨hf₀,hf₁⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hZ : AnalyticAt ℂ Z w := (globalThetaMellinIntegral_entire_of_vanishing f.val hf₀ hf₁ (χ j.val.1)).analyticAt w
  have hz : meromorphicOrderAt Z w = (n : WithTop ℤ) := hf.trans hn'.2
  rw [hZ.meromorphicOrderAt_eq] at hz
  refine ⟨f, (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hZ).mp ?_⟩
  cases h : analyticOrderAt Z w with
  | top => simp [h] at hz
  | coe r =>
    rw [h, ENat.map_natCast] at hz
    congr 1
    exact_mod_cast (WithTop.coe_eq_coe.mp hz)

/-- A character with nonzero logarithmic derivative crosses each polar weight simply. -/
private theorem stripTheta_polarFactor_order {B : ℂ → ℂ} {w d : ℂ} (hB : AnalyticAt ℂ B w)
    (hD : HasDerivAt B d w) (hd : d ≠ 0) (hw : B w = 1 ∨ B w = 2) :
    meromorphicOrderAt (fun z ↦ (B z - 2) * (B z - 1)) w = 1 := by
  let A := fun z ↦ (B z - 2) * (B z - 1)
  have ha : AnalyticAt ℂ A w := (hB.sub analyticAt_const).mul (hB.sub analyticAt_const)
  have hv : A w = 0 := by rcases hw with h | h <;> simp [A, h]
  have hda : HasDerivAt A (d * (B w - 1) + (B w - 2) * d) w :=
    (hD.sub_const _).mul (hD.sub_const _)
  have hn : deriv A w ≠ 0 := by
    rw [hda.deriv]
    rcases hw with h | h <;> norm_num [h, hd]
  have ho : analyticOrderAt A w = 1 := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (n := 1) ha).mpr
    ⟨fun k hk ↦ by simpa [Nat.lt_one_iff.mp hk] using hv, by simpa using hn⟩
  change meromorphicOrderAt A w = 1
  rw [ha.meromorphicOrderAt_eq, ho]
  rfl

/-- A double difference of the standard Gaussian removes both polar values. At
either exceptional weight its normalized Mellin factor has a simple zero. -/
private theorem stripTheta_exists_normalized_order_one (χ : PontryaginDual C𝔽) (w : ℂ)
    (he : ideleClassNormTwist χ w = 1 ∨ ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) 1) :
    ∃ f : adelePolarSubspace F,
      meromorphicOrderAt (fun z ↦ (adelicEigendistribution_normalized χ).choose z f.val) w = 1 := by
  let r : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  let g := canonicalIdeleNormSection F r
  let y : C𝔽 := QuotientGroup.mk g
  have hy : ideleClassNorm F y = r := canonicalIdeleNormSection_rightInverse F r
  let τ := schwartzBruhatUnitTranslate (R := AdeleRing (𝓞 F) F) g
  let G := adelicStandardGaussian χ
  let x := τ G - G
  let f := τ x - (2 : ℂ) • x
  let P := adelePolarValues (F := F)
  have h₀ (v : ℬ) : (P (τ v)).1 = (P v).1 := by
    change schwartzBruhatUnitTranslate g v (Multiplicative.ofAdd 0) = v (Multiplicative.ofAdd 0)
    rw [schwartzBruhatUnitTranslate_apply, mul_zero]
  have h₁ (v : ℬ) : (P (τ v)).2 = 2 * (P v).2 := by
    let K := (adelicThetaLinearMap F).ker
    have hact := (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2 g v
    have hn := globalThetaPolarValues_snd_translate y (K.mkQL v)
    have hu : (P (τ v)).2 = ((ideleClassNorm F y).val : ℝ) * (P v).2 :=
      (congrArg (fun u ↦ (globalThetaPolarValues (F := F) u).2) hact.symm).trans hn
    rw [hy] at hu
    exact hu
  have hsub : f ∈ adelePolarSubspace F := by
    change P f = 0
    have hsa : (P x).1 = 0 := by simp [x, h₀]
    ext <;> simp [f, h₀, h₁, hsa]
  refine ⟨⟨f,hsub⟩, ?_⟩
  let D := (adelicEigendistribution_normalized χ).choose
  let B := fun z ↦ ideleClassNormTwist χ z y
  have hval : (fun z ↦ D z f) = fun z ↦ (B z - 2) * (B z - 1) := by
    funext z
    have hN := ((adelicEigendistribution_normalized χ).choose_spec.2.1 z (D z)).mp rfl
    have hD (v : ℬ) : D z (τ v) = B z * D z v := hN.1 g v
    have hG : D z G = 1 := hN.2
    simp [f, x, hD, hG]
    ring
  change meromorphicOrderAt (fun z ↦ D z f) w = 1
  rw [hval]
  have hB : B = fun z ↦ (χ y : ℂ) * Complex.exp (((Real.log 2 : ℝ) : ℂ) * z) := by
    funext z
    change (χ y : ℂ) * ((((ideleClassNorm F y).val : ℝ) : ℂ) ^ z) = _
    rw [hy]
    change (χ y : ℂ) * ((2 : ℂ) ^ z) = _
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    congr 3
    norm_cast
  have hd : HasDerivAt B ((χ y : ℂ) * (Complex.exp (((Real.log 2 : ℝ) : ℂ) * w) * (Real.log 2 : ℝ))) w := by
    rw [hB]
    exact (((hasDerivAt_id w).const_mul _).cexp.const_mul _).congr_deriv (by simp)
  apply stripTheta_polarFactor_order (B := B) (by rw [hB]; fun_prop) hd
  · exact mul_ne_zero (Circle.coe_ne_zero _) (mul_ne_zero (Complex.exp_ne_zero _) (Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'))
  · rcases he with he | he
    · exact Or.inl (DFunLike.congr_fun he y)
    · refine Or.inr ((DFunLike.congr_fun he y).trans ?_)
      change 1 * ((((ideleClassNorm F y).val : ℝ) : ℂ) ^ (1 : ℂ)) = 2
      rw [hy, Complex.cpow_one, one_mul]
      rfl

/-- Paper: Theorems 3.4.3.3(2), p. 153, and 10.2.2.1, p. 446. At each fixed
point, the minimum vanishing order over all entire polar-free theta Mellin
transforms is the positive part of the completed Hecke divisor there.
Deviation: This pointwise consequence uses the Gaussian-normalized factorization
with its nonzero Tamagawa scalar. It includes both simple poles after cancellation. -/
theorem isLeast_globalThetaMellinIntegral_orders (χ : PontryaginDual C𝔽) (w : ℂ) :
    IsLeast (Set.range fun f : adelePolarSubspace F ↦
      meromorphicOrderAt (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) w)
      (max 0 (meromorphicOrderAt (continuedCompletedHeckeL χ) w)) := by
  let Z (f : adelePolarSubspace F) (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
  let L := continuedCompletedHeckeL χ
  have hZ (f : adelePolarSubspace F) : 0 ≤ meromorphicOrderAt (Z f) w := by
    obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
    exact (globalThetaMellinIntegral_entire_of_vanishing f.val hf hf' χ |>.analyticAt w).meromorphicOrderAt_nonneg
  refine ⟨?_, ?_⟩
  · by_cases he : ideleClassNormTwist χ w = 1 ∨
        ideleClassNormTwist χ w = ideleClassNormTwist (1 : PontryaginDual C𝔽) 1
    · obtain ⟨f, hf⟩ := stripTheta_exists_normalized_order_one χ w he
      have hp : meromorphicOrderAt L w = -1 := continuedCompletedHeckeL_order_of_exceptional χ w he
      have h := (stripTheta_mellin_factor_order χ f w).2
      refine ⟨f, ?_⟩
      change meromorphicOrderAt (Z f) w = max 0 (meromorphicOrderAt L w)
      exact h.trans (by rw [hf, hp]; decide)
    · obtain ⟨f,hf⟩ := exists_globalThetaMellinIntegral_order_eq_of_regular χ w (not_or.mp he).1 (not_or.mp he).2
      exact ⟨f, hf.trans (max_eq_right (hf ▸ hZ f)).symm⟩
  · rintro _ ⟨f,rfl⟩
    exact max_le (hZ f) (stripTheta_mellin_order χ f w).1

/-- The unweighted Haar integral of a weighted polar-free theta function against an
admitted zero jet vanishes, including the center shift in its multiplicity. -/
private theorem stripTheta_weighted_moment_zero (χ : PontryaginDual C𝔽)
    (f : adelePolarSubspace F) (a b t : ℝ) (k : ℕ)
    (hk : k < (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(a + b, t))).untop₀.toNat) :
    ∫ g, modulationWeight m𝔽 a (adelicTheta f.val) g * spectralZeroJet χ b t k g ∂μ𝔽 = 0 := by
  let χq : QuasiCharacter C𝔽 :=
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hi := globalThetaMellinIntegral_integrable_of_vanishing f.val hf hf'
  have hz : (shift(a + b, t)).re ∈ Ioo (a+b-1) (a+b+1) := by simp
  obtain ⟨_, _, hderiv⟩ := iteratedDeriv_normTwist_moment m𝔽 μ𝔽 χq
    (fun σ _ n ↦ spectralLineJet_functional_moment m𝔽 μ𝔽 χq (adelicTheta f.val) hi σ n) k hz
  have h : (∫ g, modulationWeight m𝔽 a (adelicTheta f.val) g * spectralZeroJet χ b t k g ∂μ𝔽) =
      iteratedDeriv k (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)) (shift(a+b,t)) := by
    refine (integral_congr_ae (ae_of_all _ fun g ↦ ?_)).trans hderiv.symm
    have hpos : 0 < ((m𝔽 g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    change ((((m𝔽 g).val : ℝ) ^ a : ℝ) : ℂ) * adelicTheta f.val g *
        (quasiCharacterNormTwist (m𝔽).toMonoidHom (m𝔽).continuous χq (shift(b,t)) g * (logNorm g : ℂ)^k) =
      adelicTheta f.val g * (logNorm g : ℂ)^k *
        quasiCharacterNormTwist (m𝔽).toMonoidHom (m𝔽).continuous χq (shift(a+b,t)) g
    rw [quasiCharacterNormTwist_eq_exp, quasiCharacterNormTwist_eq_exp,
      Real.rpow_def_of_pos hpos, Complex.ofReal_exp, Complex.ofReal_mul]
    have e : Complex.exp ((shift(a+b,t)) * (logNorm g : ℂ)) =
        Complex.exp ((logNorm g : ℂ) * (a : ℂ)) * Complex.exp ((shift(b,t)) * (logNorm g : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    change Complex.exp ((logNorm g : ℂ) * (a : ℂ)) * adelicTheta f.val g *
        (χq g * Complex.exp ((shift(b,t)) * (logNorm g : ℂ)) * (logNorm g : ℂ)^k) =
      adelicTheta f.val g * (logNorm g : ℂ)^k * (χq g * Complex.exp ((shift(a+b,t)) * (logNorm g : ℂ)))
    rw [e]
    ring
  exact h.trans (stripTheta_mellin_zero χ f _ k hk)

/-- Paper: Theorem 10.2.2.1, p. 446. Every strip jet annihilates the closed
weighted polar-free theta image.
Deviation: At a strip endpoint the jet order must be strictly below (s − 1) / 2. -/
theorem spectralStripJet_commonKernel_forward (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (y : W(-α, α, s))
    (hy : y ∈ globalThetaSobolev F a (stripI(hα)) hs) (j : SpectralStripJetIndex χ a α s) :
    spectralSobolevPairing y ((spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))) = 0 := by
  let u : W'(-α, α, s) := (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (stripI(hα)) hs).exists.choose
  let Λ := T.symm u
  have hp (v : W(-α, α, s)) : Λ v = spectralSobolevPairing v u :=
    (spectralSobolevPairing_dual (stripI(hα)) hs Λ v).2.trans
      (congrArg (spectralSobolevPairing v) (T.apply_symm_apply u))
  have habs : μ𝔽 ≪ L2μ'(-α, α, s) :=
    withDensity_absolutelyContinuous' (symmIntervalSobolevDensity_inv_continuous hα s).measurable.ennreal_ofReal.aemeasurable
      (.of_forall fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (symmIntervalSobolevDensity_pos hα s (logNorm g))))
  have hrep : (u : C𝔽 → ℂ) =ᵐ[μ𝔽] stripJet(χ, j) := habs.ae_le (MemLp.coeFn_toLp _)
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (stripI(hα)) hs).exists.choose
  have hgen (f : adelePolarSubspace F) : Λ (E (Submodule.Quotient.mk f)) = 0 := by
    rw [hp]
    have hE := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (stripI(hα)) hs).exists.choose_spec.2 f
    have hN {b : ℝ} (N : ℕ) : spectralStripMultiplicity α s b N ≤ N := by
      unfold spectralStripMultiplicity spectralBoundaryMultiplicity
      split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _
    exact (integral_congr_ae (hE.mul hrep)).trans (stripTheta_weighted_moment_zero
      (χ j.val.1) f a j.val.2.1 j.val.2.2.1 j.val.2.2.2 (j.property.trans_le (hN _)))
  have hR : E.toLinearMap.range ≤ Λ.ker := by
    rintro _ ⟨v, rfl⟩
    induction v using Submodule.Quotient.induction_on with
    | H f => exact hgen f
  exact (hp y).symm.trans ((E.toLinearMap.range.topologicalClosure_minimal hR Λ.isClosed_ker) hy)

end StripThetaAnnihilation

namespace StripInterpolation

/-- Removing some of a finite-order zero within the entire Schwartz–Bergman space
preserves the orders at every other point. -/
private theorem divide_at_point {f : ℂ → ℂ} (hf : f ∈ schwartzBergmanSubmodule univ)
    (w : ℂ) {n k : ℕ} (horder : analyticOrderAt f w = n) (hk : k ≤ n) :
    ∃ q : ℂ → ℂ, q ∈ schwartzBergmanSubmodule univ ∧ analyticOrderAt q w = k ∧
      ∀ v ≠ w, analyticOrderAt q v = analyticOrderAt f v := by
  classical
  have hd : Differentiable ℂ f := differentiableOn_univ.mp (by simpa using hf.2.1)
  obtain ⟨g, hg, hgw, hnear⟩ := (hd.analyticAt w).analyticOrderAt_eq_natCast.mp horder
  let d := n - k
  have hnk : d + k = n := Nat.sub_add_cancel hk
  let q (z : ℂ) := if z = w then (z - w)^k * g z else f z / (z - w)^d
  have hlocal : q =ᶠ[𝓝 w] fun z ↦ (z - w)^k * g z := by
    filter_upwards [hnear] with z he
    by_cases hz : z = w
    · simp [q, hz]
    · simp only [q, ite_eq_right hz]
      rw [div_eq_iff (pow_ne_zero _ (sub_ne_zero.mpr hz)), he, ← hnk, pow_add]
      simp only [smul_eq_mul]
      ring
  have ha : AnalyticAt ℂ q w :=
    ((analyticAt_id.sub analyticAt_const).pow k |>.mul hg).congr hlocal.symm
  have hother {v : ℂ} (hv : v ≠ w) :
      q =ᶠ[𝓝 v] fun z ↦ f z / (z - w)^d := by
    filter_upwards [eventually_ne_nhds hv] with z hz using ite_eq_right hz
  have hdq : Differentiable ℂ q := by
    intro z
    by_cases hz : z = w
    · simpa [hz] using ha.differentiableAt
    · have hh : DifferentiableAt ℂ (fun u : ℂ ↦ f u / (u - w)^d) z :=
        (hd z).div ((differentiableAt_id.sub_const w).pow d) (pow_ne_zero d (sub_ne_zero.mpr hz))
      exact hh.congr_of_eventuallyEq (hother hz)
  refine ⟨q, ⟨by simp, by simpa using hdq.differentiableOn (s := univ), ?_⟩,
    ha.analyticOrderAt_eq_natCast.mpr ⟨g, hg, hgw, hlocal⟩, ?_⟩
  · intro a b hab hI N
    obtain ⟨B, hB⟩ := hf.2.2 a b hab hI N
    have hc : Continuous (fun z : ℂ ↦ ‖z^N * q z‖) :=
      ((continuous_id.pow N).mul hdq.continuous).norm
    obtain ⟨C, hC⟩ := (isCompact_closedBall w 1).bddAbove_image hc.continuousOn
    refine ⟨max C B, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    by_cases hdist : z ∈ Metric.closedBall w 1
    · exact (hC ⟨z, hdist, rfl⟩).trans (le_max_left _ _)
    · have hnorm : 1 < ‖z - w‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hdist
      have hne : z ≠ w := by rintro rfl; norm_num at hnorm
      change ‖z^N * q z‖ ≤ max C B
      rw [show q z = f z / (z - w)^d from ite_eq_right hne, ← mul_div_assoc, norm_div, norm_pow]
      exact (div_le_self (norm_nonneg _) (one_le_pow₀ hnorm.le)).trans
        ((hB ⟨z, hz, rfl⟩).trans (le_max_right _ _))
  · intro v hv
    have hmul : f =ᶠ[𝓝 v] fun z ↦ (z - w)^d * q z := by
      filter_upwards [hother hv, eventually_ne_nhds hv] with z hq hz
      rw [hq]
      field_simp
    have hor : analyticOrderAt (fun z : ℂ ↦ (z - w)^d) v = 0 :=
      (AnalyticAt.analyticOrderAt_eq_zero (by fun_prop)).mpr (pow_ne_zero _ (sub_ne_zero.mpr hv))
    rw [analyticOrderAt_congr hmul, analyticOrderAt_fun_mul (by fun_prop) (hdq.analyticAt v), hor, zero_add]

/-- Gaussian damping converts an entire function bounded on closed vertical substrips
to an entire Schwartz–Bergman function without changing any vanishing orders. -/
private theorem gaussian_of_strip_bound {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hb : ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ ≤ C) :
    (fun z ↦ Complex.exp (z^2) * f z) ∈ schwartzBergmanSubmodule univ ∧
    ∀ z, analyticOrderAt (fun u ↦ Complex.exp (u^2) * f u) z = analyticOrderAt f z := by
  let e (z : ℂ) := Complex.exp (z^2)
  have ha : Differentiable ℂ e := by dsimp [e]; fun_prop
  have he : e ∈ schwartzBergmanSubmodule univ := by
    simpa [e] using gaussian_mem_schwartzBergmanSubmodule univ isOpen_univ
  refine ⟨⟨by simp, (ha.mul hd).differentiableOn, ?_⟩, ?_⟩
  · intro a b hab hI N
    obtain ⟨A, hA⟩ := he.2.2 a b hab hI N
    obtain ⟨C, hC⟩ := hb a b hab
    refine ⟨max A 0 * max C 0, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖z^N * (e z * f z)‖ ≤ _
    rw [← mul_assoc, norm_mul]
    exact mul_le_mul ((hA ⟨z, hz, rfl⟩).trans (le_max_left _ _))
      ((hC z hz).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  · intro z
    have h0 := (ha.analyticAt z).analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _)
    change analyticOrderAt (fun u ↦ e u * f u) z = _
    rw [analyticOrderAt_fun_mul (ha.analyticAt z) (hd.analyticAt z), h0, zero_add]

/-- A two-sided Laplace integral absolutely convergent at both real endpoints is
bounded uniformly across that closed complex substrip. -/
private theorem laplace_strip_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : X → ℂ) (l : X → ℝ) (h : ∀ t : ℝ,
      Integrable (fun x ↦ u x * Complex.exp ((t : ℂ) * (l x : ℂ))) μ) (a b : ℝ) :
    ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b →
      ‖∫ x, u x * Complex.exp (z * (l x : ℂ)) ∂μ‖ ≤ C := by
  let M (r : ℝ) (x : X) := ‖u x * Complex.exp ((r : ℂ) * (l x : ℂ))‖
  refine ⟨∫ x, M a x + M b x ∂μ, fun z hz ↦
    norm_integral_le_of_norm_le ((h a).norm.add (h b).norm) (ae_of_all _ fun x ↦ ?_)⟩
  have he (v : ℂ) : ‖u x * Complex.exp (v * (l x : ℂ))‖ =
      ‖u x‖ * Real.exp (v.re * l x) := by simp [Complex.norm_exp, Complex.mul_re]
  by_cases hxl : 0 ≤ l x
  · apply (le_add_of_nonneg_left (a := M b x) (norm_nonneg _)).trans'
    dsimp only [M]
    rw [he, he, Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz.2 hxl)) (norm_nonneg _)
  · apply (le_add_of_nonneg_right (a := M a x) (norm_nonneg _)).trans'
    dsimp only [M]
    rw [he, he, Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hz.1 (le_of_not_ge hxl))) (norm_nonneg _)

/-- A triangular collection in a linear subspace interpolates all the coordinates
of one finite jet. -/
private theorem finite_interpolation {n : ℕ} (S : Submodule ℂ (Fin n → ℂ))
    (hpivot : ∀ j : Fin n, ∃ v ∈ S, (∀ i < j, v i = 0) ∧ v j ≠ 0)
    (c : Fin n → ℂ) : c ∈ S := by
  have he (k : ℕ) (hk : k ≤ n) : ∃ v ∈ S, ∀ i : Fin n, (i : ℕ) < k → v i = c i := by
    induction k with
    | zero => exact ⟨0, S.zero_mem, by simp⟩
    | succ k ih =>
      obtain ⟨v, hv, hvi⟩ := ih (by omega)
      let j : Fin n := ⟨k, by omega⟩
      obtain ⟨u, hu, hu0, huj⟩ := hpivot j
      let d := (c j - v j) / u j
      refine ⟨v + d • u, S.add_mem hv (S.smul_mem d hu), ?_⟩
      intro i hi
      by_cases hik : (i : ℕ) < k
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu0 i hik, mul_zero, add_zero, hvi i hik]
      · have hij : i = j := Fin.ext (by change (i : ℕ) = k; omega)
        subst i
        change v j + (c j - v j) / u j * u j = c j
        rw [div_mul_cancel₀ _ huj]
        ring
  obtain ⟨v, hv, hvc⟩ := he n le_rfl
  exact (funext fun i ↦ hvc i i.isLt) ▸ hv

/-- Exact order at one zero and the required vanishing at other zeros produce an
entire Schwartz–Bergman transform with arbitrary prescribed finite jet at that point. -/
private theorem interpolate_transform {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hb : ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ ≤ C)
    (w : ℂ) (n : ℕ) (horder : analyticOrderAt f w = n) (c : Fin n → ℂ) :
    ∃ H : schwartzBergmanSubmodule univ,
      (∀ i : Fin n, iteratedDeriv i.val H.val w = c i) ∧
      ∀ v ≠ w, ∀ m : ℕ, (∀ k < m, iteratedDeriv k f v = 0) →
        ∀ k < m, iteratedDeriv k H.val v = 0 := by
  let B := schwartzBergmanSubmodule univ
  have han (H : B) : Differentiable ℂ H.val := differentiableOn_univ.mp (by simpa using H.property.2.1)
  let ev (z : ℂ) (i : ℕ) : B →ₗ[ℂ] ℂ := {
    toFun H := iteratedDeriv i H.val z
    map_add' u v := iteratedDeriv_fun_add ((han u).analyticAt z).contDiffAt ((han v).analyticAt z).contDiffAt
    map_smul' c u := iteratedDeriv_fun_const_smul_field c u.val }
  let index := {p : ℂ × ℕ × ℕ //
    p.1 ≠ w ∧ p.2.2 < p.2.1 ∧ (∀ k < p.2.1, iteratedDeriv k f p.1 = 0)}
  let V : Submodule ℂ B := ⨅ p : index, (ev p.val.1 p.val.2.2).ker
  let A : B →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi fun i ↦ ev w i.val
  have hV (v : B) : v ∈ V ↔ ∀ p : index, iteratedDeriv p.val.2.2 v.val p.val.1 = 0 := by
    simp only [V, Submodule.mem_iInf, LinearMap.mem_ker, ev, LinearMap.coe_mk, AddHom.coe_mk]
  let g (z : ℂ) := Complex.exp (z^2) * f z
  obtain ⟨hg, hgo⟩ := gaussian_of_strip_bound hd hb
  have hs := finite_interpolation (V.map A) (fun (i : Fin n) ↦ ?_) c
  · obtain ⟨H, hH, hc⟩ := hs
    refine ⟨H, fun i ↦ congrFun hc i, fun v hv m hm k hk ↦ ?_⟩
    exact (hV H).mp hH ⟨(v, m, k), hv, hk, hm⟩
  · obtain ⟨q, hq, hw, haway⟩ := divide_at_point (f := g) hg w ((hgo w).trans horder) i.isLt.le
    let Q : B := ⟨q, hq⟩
    have hpivot := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ((han Q).analyticAt w)).mp hw
    refine ⟨A Q, ⟨Q, (hV Q).mpr ?_, rfl⟩, fun j hj ↦ hpivot.1 j hj, hpivot.2⟩
    intro ⟨⟨v, m, k⟩, hv, hk, hm⟩
    have ho := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hd.analyticAt v)).mpr hm
    rw [← hgo v, ← haway v hv] at ho
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((han Q).analyticAt v)).mp ho k hk
/-- Starting from a biorthogonal family, the other biorthogonal families are
exactly its translations by one common-kernel vector per index. -/
private theorem density_iff {J E : Type*} [AddCommGroup E] [Module ℂ E]
    (L : J → E →ₗ[ℂ] ℂ) (D : (J → E) → Prop) (v : J → E)
    (hv : ∀ i, L i (v i) = 1) (hz : ∀ i j, i ≠ j → L j (v i) = 0) :
    (∃ y : J → E, (∀ i, L i (y i) = 1) ∧
        (∀ i j, i ≠ j → L j (y i) = 0) ∧ D y) ↔
      ∃ r : J → E, (∀ i j, L j (r i) = 0) ∧ D (fun i ↦ v i + r i) := by
  constructor
  · rintro ⟨y, hone, hzero, hy⟩
    refine ⟨fun i ↦ y i - v i, fun i j ↦ ?_, ?_⟩
    · rw [map_sub]
      by_cases e : i = j
      · subst j
        simp [hone, hv]
      · simp [hzero i j e, hz i j e]
    · have he (i : J) : v i + (y i - v i) = y i := by abel
      simpa only [he] using hy
  · rintro ⟨r, hr, hy⟩
    refine ⟨fun i ↦ v i + r i, fun i ↦ ?_, fun i j hij ↦ ?_, hy⟩
    · simp [hv, hr]
    · simp [hz i j hij, hr]

end StripInterpolation

section StripProfileInterpolation

/-- An integral supported on a nontrivial compact character vanishes by Haar invariance. -/
private theorem stripProfile_orthogonality {G : Type*} [CommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [MeasurableMul₂ G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (χ η : PontryaginDual G) (g : G) (hg : χ g ≠ η g)
    (q : G → ℂ) (hq : ∀ x, q (g * x) = q x) :
    (∫ x, ((χ x : ℂ)⁻¹ * (η x : ℂ)) * q x ∂μ) = 0 := by
  let v (x : G) := (χ x : ℂ)⁻¹ * (η x : ℂ)
  have hmul (x : G) : v (g * x) = v g * v x := by
    dsimp [v]
    rw [map_mul, map_mul, Circle.coe_mul, Circle.coe_mul, mul_inv_rev]
    ring
  have hne : v g ≠ 1 := by
    intro he
    apply hg
    apply Subtype.ext
    exact (inv_mul_eq_one₀ (Circle.coe_ne_zero _)).mp he
  let A := ∫ x, v x * q x ∂μ
  have h : A = v g * A :=
    (integral_mul_left_eq_self (μ := μ) (fun x ↦ v x * q x) g).symm.trans <| by
      rw [← integral_const_mul]
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      change v (g * x) * q (g * x) = v g * (v x * q x)
      rw [hmul, hq, mul_assoc]
  change A = 0
  exact (mul_eq_zero.mp (by linear_combination -h : (v g - 1) * A = 0)).resolve_left (sub_ne_zero.mpr hne)

/-- The physical strip jet is the chosen compact character times an exponential polynomial. -/
private theorem stripProfile_jet (χ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (x : C𝔽) :
    spectralZeroJet χ b t k x = (χ x : ℂ) * Complex.exp (shift(b, t) * (logNorm x : ℂ)) *
      (logNorm x : ℂ)^k := by
  let η : QuasiCharacter C𝔽 := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  exact congrArg (fun u : ℂ ↦ u * (logNorm x : ℂ)^k) (quasiCharacterNormTwist_eq_exp m𝔽 η _ _)

/-- Pullback from weighted radial L² with the inverse base character. -/
private theorem stripTail_radial_lift (ψ : PontryaginDual C𝔽) {α s : ℝ} (_hα : 0 ≤ α) (_hs : 0 ≤ s) :
    ∃ L : CompactIntervalSobolev volume id (-α) α s →L[ℂ] W(-α, α, s), ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽]
      fun x ↦ (ψ x : ℂ)⁻¹ * f (logNorm x) := by
  let ν := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let E := globalThetaAmbient_equiv_canonical (F := F) hm𝔽 (-α) α s
  let R := sobolev_character_pull m𝔽 hm𝔽 hms𝔽 _ (continuous_intervalSobolevDensity' (-α) α s)
    (intervalSobolevDensity_pos (-α) α s) (fun x ↦ (ψ⁻¹ x : ℂ)) (continuous_subtype_val.comp ψ⁻¹.continuous)
    (fun _ ↦ Circle.norm_coe _)
  let L := E.choose.symm.toContinuousLinearMap.comp R.choose
  refine ⟨L, fun f ↦ (E.choose_spec (L f)).1.symm.trans ?_⟩
  rw [show E.choose (L f) = R.choose f from E.choose.apply_symm_apply _]
  apply (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 ν).ae_eq
  refine (R.choose_spec f).trans (.of_forall fun x ↦ ?_)
  change (((ψ x)⁻¹ : Circle) : ℂ) * f (logNorm x) = (ψ x : ℂ)⁻¹ * f (logNorm x)
  rw [Circle.coe_inv]

/-- Every scalar two-sided exponential-decay profile lifts to the ambient strip
Sobolev space in the inverse base-character component. -/
private theorem stripProfile_sobolev (χ : PontryaginDual C𝔽) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (p : PositiveRealExponentialDecay univ) :
    ∃ y : W(-α, α, s), (y : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ x : ℂ)⁻¹ * p.val (logNorm x) := by
  obtain ⟨L, hL⟩ := stripTail_radial_lift χ hα hs
  let P := scalarIntervalSobolev_dense (-α) α s (stripI(hα)) hs univ isOpen_univ
    ordConnected_univ (subset_univ _)
  let ν := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  refine ⟨L (P.choose p), (hL _).trans ?_⟩
  apply (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 ν).ae_eq
  have he := (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽).quasiMeasurePreserving.ae_eq_comp (P.choose_spec.2.2 p)
  filter_upwards [he] with x hx using congrArg ((χ x : ℂ)⁻¹ * ·) hx

/-- Finite order strip moments of inverse profiles on a wider open interval. -/
private theorem stripProfile_log_moment {I : Set ℝ} (hI : IsOpen I) (h0 : (0 : ℝ) ∈ I)
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hl : MeasurePreserving logNorm ν volume)
    (p : PositiveRealExponentialDecay I) (k : ℕ) (z : ℂ) (hz : z.re ∈ I) :
    (∫ x : C𝔽, (((logNorm x : ℂ)^k) * p.val (logNorm x)) * Complex.exp (z * (logNorm x : ℂ)) ∂μ𝔽) =
      ((Measure.haarScalarFactor μ𝔽 ν : ℝ) : ℂ) *
        iteratedDeriv k (mellin (fun t ↦ p.val (Real.log t))) z := by
  rw [scalarDecay_mellin_deriv hI p k hz, mellin_logProfile (fun t : ℝ ↦ (t : ℂ)^k * p.val t)]
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν, integral_smul_nnreal_measure]
  rw [NNReal.smul_def, Complex.real_smul]
  congr 1
  have hp : Continuous p.val := by
    refine (logExponentialDecayTwist I ⟨0, h0⟩ p).continuous.congr fun t ↦ ?_
    simpa using logExponentialDecayTwist_apply I ⟨0, h0⟩ p t
  let q (t : ℝ) := (t : ℂ)^k * p.val t * Complex.exp (z * (t : ℂ))
  have hq : Continuous q := ((Complex.continuous_ofReal.pow k).mul hp).mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  exact (integral_map hl.measurable.aemeasurable (f := q) hq.aestronglyMeasurable).symm.trans
    (congrArg (fun η : Measure ℝ ↦ ∫ t, q t ∂η) hl.map_eq)

end StripProfileInterpolation

/-- Paper: Theorem 10.2.2.1, p. 446. The discrete divisor in each norm
chart gives countably many strip jets over the countable norm-one dual. -/
theorem spectralStripJet_countable (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a α s : ℝ) :
    Countable (SpectralStripJetIndex χ a α s) := by
  have hK : IsCompact ((ideleClassNorm F).ker : Set C𝔽) :=
    IsModulation.isCompact_ker (m := m𝔽) hm𝔽
  let : CompactSpace C₁ := isCompact_iff_compactSpace.mp hK
  let : LocallyCompactSpace C₁ := hK.isClosed.locallyCompactSpace
  let : SecondCountableTopology C₁ := Topology.IsInducing.subtypeVal.secondCountableTopology
  let : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual C₁) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap C₁ Circle).secondCountableTopology
  let : Countable (PontryaginDual C₁) := countable_of_Lindelof_of_discrete
  let Z (ω : PontryaginDual C₁) := {z : ℂ | 0 < multiplicity(χ ω, z)}
  have hc (ω : PontryaginDual C₁) : (Z ω).Countable := by
    have hm := (continuedCompletedHeckeL_spec (χ ω)).1.meromorphicOn
    have hcod : (Z ω)ᶜ ∈ Filter.codiscrete ℂ := by
      filter_upwards [hm.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top] with z hz
      rcases hz.2 with h | h <;> simp [Z, h]
    let : DiscreteTopology (Z ω) := isDiscrete_iff_discreteTopology.mp
      (compl_mem_codiscrete_iff.mp hcod).2
    exact Set.countable_coe_iff.mp countable_of_Lindelof_of_discrete
  let W := ⋃ ω, Z ω
  let : Countable W := (Set.countable_iUnion hc).to_subtype
  have hz (j : SpectralStripJetIndex χ a α s) : shift(a + j.val.2.1, j.val.2.2.1) ∈ W := by
    apply Set.mem_iUnion.mpr
    refine ⟨j.val.1, ?_⟩
    have h := j.property
    change 0 < multiplicity(χ j.val.1, shift(a + j.val.2.1, j.val.2.2.1))
    unfold spectralStripMultiplicity spectralBoundaryMultiplicity at h
    split_ifs at h <;> omega
  let e (j : SpectralStripJetIndex χ a α s) : PontryaginDual C₁ × W × ℕ :=
    (j.val.1, ⟨shift(a + j.val.2.1, j.val.2.2.1), hz j⟩, j.val.2.2.2)
  apply Function.Injective.countable (f := e)
  intro i j hij
  have hre := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.1.val.re) hij
  have him := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.1.val.im) hij
  have hω := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.1) hij
  have hk := congrArg (fun p : PontryaginDual C₁ × W × ℕ ↦ p.2.2) hij
  exact Subtype.ext (Prod.ext hω (Prod.ext (by simpa [e] using hre) (Prod.ext (by simpa [e] using him) hk)))

namespace StripMultiplier

/-- Pointwise convergence to zero under an L² envelope gives convergence in L². -/
private theorem l2_dominated {X ι : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter ι}
    [l.IsCountablyGenerated] (u : ι → X → ℂ) (hu : ∀ n, MemLp (u n) 2 μ)
    (f : X → ℂ) (hf : MemLp f 2 μ) (hbound : ∀ n x, ‖u n x‖ ≤ 2 * ‖f x‖)
    (hlim : ∀ x, Tendsto (fun n ↦ u n x) l (𝓝 0)) :
    Tendsto (fun n ↦ (eLpNorm (u n) 2 μ).toReal) l (𝓝 0) := by
  let D (n : ι) (x : X) := ‖u n x‖ ^ 2
  have h : Tendsto (fun n ↦ ∫ x, D n x ∂μ) l (𝓝 (∫ _ : X, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ 4 * ‖f x‖ ^ 2)
    · exact .of_forall fun n ↦ (hu n).aestronglyMeasurable.norm.pow 2
    · refine .of_forall fun n ↦ .of_forall fun x ↦ ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc
        _ ≤ (2 * ‖f x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hbound n x) _
        _ = _ := by ring
    · exact hf.norm.integrable_sq.const_mul 4
    · exact .of_forall fun x ↦ by simpa [D] using (hlim x).norm.pow 2
  have hs (n : ι) : ‖(hu n).toLp _‖ ^ 2 = ∫ x, D n x ∂μ := by
    rw [← L2.integral_sq_norm (𝕜 := ℂ)]
    exact integral_congr_ae ((hu n).coeFn_toLp.fun_comp fun t ↦ ‖t‖ ^ 2)
  simpa only [integral_zero, comp_def, ← hs, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero,
    Lp.norm_toLp, Real.sqrt_sq ENNReal.toReal_nonneg] using (Real.continuous_sqrt.tendsto _).comp h

/-- A bounded holomorphic multiplier preserves the entire family of substrip
bounds in the Schwartz–Bergman space. -/
private theorem multiply_mem {I : Set ℝ} (H : SchwartzBergman I) (b : ℂ → ℂ)
    (hb : DifferentiableOn ℂ b (Complex.re ⁻¹' I)) (hc : ∀ z, z.re ∈ I → ‖b z‖ ≤ 1) :
    (fun z ↦ b z * H.val z) ∈ schwartzBergmanSubmodule I := by
  refine ⟨fun z hz ↦ ?_, hb.mul H.property.2.1, ?_⟩
  · exact (congrArg (b z * ·) (H.property.1 hz)).trans (mul_zero _)
  · intro a c hac hsub k
    obtain ⟨M, hM⟩ := H.property.2.2 a c hac hsub k
    refine ⟨M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖z ^ k * (b z * H.val z)‖ ≤ M
    rw [mul_left_comm, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hc z (hsub hz))).trans (hM ⟨z, hz, rfl⟩)

/-- Multiplication by bounded, pointwise convergent analytic multipliers converges
in the full Schwartz–Bergman topology on the open strip. -/
private theorem tendsto_multiply {I : Set ℝ} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (H : SchwartzBergman I) (b : ι → ℂ → ℂ) (hb : ∀ n, DifferentiableOn ℂ (b n) (Complex.re ⁻¹' I))
    (hc : ∀ n z, z.re ∈ I → ‖b n z‖ ≤ 1)
    (hl : ∀ z, z.re ∈ I → Tendsto (fun n ↦ b n z) l (𝓝 1)) :
    let G (n : ι) : SchwartzBergman I := ⟨_, multiply_mem H (b n) (hb n) (hc n)⟩
    Tendsto G l (𝓝 H) := by
  intro G
  let P (i : I × ℕ) : Seminorm ℂ (schwartzBergmanSubmodule I) :=
    Seminorm.of (fun f ↦ (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
      (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  apply ((withGeneratingSeminorms_spec (schwartzBergmanSubmodule I) P).tendsto_nhds G H).mpr
  rintro ⟨a, k⟩ ε hε
  let z (t : ℝ) := (a.val : ℂ) + t * Complex.I
  have hz (t : ℝ) : (z t).re ∈ I := by simp [z]
  let F := weightedVerticalTrace a k H.val
  let U (n : ι) := weightedVerticalTrace a k (G n - H).val
  have hU (n : ι) (t : ℝ) : U n t = (b n (z t) - 1) * F t := by
    change (z t)^k * (b n (z t) * H.val (z t) - H.val (z t)) = (b n (z t) - 1) * ((z t)^k * H.val (z t))
    ring
  have hB (n : ι) (t : ℝ) : ‖U n t‖ ≤ 2 * ‖F t‖ := by
    rw [hU, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ‖b n (z t)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith [hc n (z t) (hz t)]
  have ht (t : ℝ) : Tendsto (fun n ↦ U n t) l (𝓝 0) := by
    simp only [hU]
    simpa using ((hl (z t) (hz t)).sub_const (1 : ℂ)).mul_const (F t)
  have hx := l2_dominated U (fun n ↦ schwartzBergman_trace_memLp I a 2 (by norm_num)
    (by norm_num) k (G n - H)) F (schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) k H) hB ht
  exact hx.eventually (gt_mem_nhds hε)

/-- Inverse Fourier–Mellin transform transports bounded cutoff convergence to the
exponential test topology, hence to the norm on every enclosed Sobolev interval. -/
private theorem scalar_approximation {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I) (hne : I.Nonempty)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (b : ι → ℂ → ℂ) (hb : ∀ n, DifferentiableOn ℂ (b n) (Complex.re ⁻¹' I))
    (hc : ∀ n z, z.re ∈ I → ‖b n z‖ ≤ 1)
    (hl : ∀ z, z.re ∈ I → Tendsto (fun n ↦ b n z) l (𝓝 1)) (p : PositiveRealExponentialDecay I) :
    ∃ q : ι → PositiveRealExponentialDecay I, Tendsto q l (𝓝 p) ∧
      ∀ n, EqOn (mellin (fun t ↦ (q n).val (Real.log t)))
        (fun z ↦ b n z * mellin (fun t ↦ p.val (Real.log t)) z) (Complex.re ⁻¹' I) := by
  let M := positiveRealFourierMellin I hI hInt hne
  let H := M p
  let G (n : ι) : SchwartzBergman I := ⟨_, multiply_mem H (b n) (hb n) (hc n)⟩
  let q (n : ι) := M.symm (G n)
  refine ⟨q, ?_, fun n z hz ↦ ?_⟩
  · have hG : Tendsto G l (𝓝 H) := tendsto_multiply H b hb hc hl
    have hq : Tendsto q l (𝓝 (M.symm H)) := (M.symm.continuous.tendsto H).comp hG
    exact (M.symm_apply_apply p) ▸ hq
  · have hn := positiveRealFourierMellin_apply I hI hInt hne (q n) z hz
    have hp := positiveRealFourierMellin_apply I hI hInt hne p z hz
    calc
      _ = (M (q n)).val z := hn.symm
      _ = (G n).val z := congrArg (fun A : SchwartzBergman I ↦ A.val z) (M.apply_symm_apply _)
      _ = _ := congrArg (b n z * ·) hp

/-- If the cutoff has the prescribed zero multiplicity, every lower moment of the
cutoff profile vanishes. -/
private theorem lower_jet_zero {I : Set ℝ} (hI : IsOpen I) (p q : PositiveRealExponentialDecay I)
    (b : ℂ → ℂ) (hb : DifferentiableOn ℂ b (Complex.re ⁻¹' I))
    (he : EqOn (mellin (fun t ↦ q.val (Real.log t)))
      (fun z ↦ b z * mellin (fun t ↦ p.val (Real.log t)) z) (Complex.re ⁻¹' I))
    (hInt : OrdConnected I) (z : ℂ) (hz : z.re ∈ I) {m k : ℕ}
    (hm : (m : ℕ∞) ≤ analyticOrderAt b z) (hk : k < m) :
    iteratedDeriv k (mellin (fun t ↦ q.val (Real.log t))) z = 0 := by
  let M := positiveRealFourierMellin I hI hInt ⟨z.re, hz⟩
  let H := M p
  have hopen := hI.preimage Complex.continuous_re
  have had : AnalyticAt ℂ b z := hb.analyticAt (hopen.mem_nhds hz)
  have Hanalytic : AnalyticAt ℂ H.val z := H.property.2.1.analyticAt (hopen.mem_nhds hz)
  have hnear : mellin (fun t ↦ q.val (Real.log t)) =ᶠ[𝓝 z] fun w ↦ b w * H.val w := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact (he hw).trans (congrArg (b w * ·) (positiveRealFourierMellin_apply I hI hInt _ p w hw).symm)
  rw [hnear.iteratedDeriv_eq]
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (had.mul Hanalytic)).mp _ k hk
  change (m : ℕ∞) ≤ analyticOrderAt (fun w ↦ b w * H.val w) z
  rw [analyticOrderAt_fun_mul had Hanalytic]
  exact le_trans hm (le_self_add)

end StripMultiplier

section StripSingleJets
open scoped Classical
local notation "Jχ(" χ ", " a ", " α ", " s ")" => SpectralStripJetIndex χ a α s
local notation "Zj(" i ")" => shift((i).val.2.1, (i).val.2.2.1)
local notation "dj(" i ")" => (i).val.2.2.2

/-- The Mellin transform of a polar-free generator is uniformly bounded on each
closed vertical substrip, including after a translation of the center. -/
private theorem stripProfile_theta_strip_bound (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F)
    (a : ℝ) :
    let Z := fun z : ℂ ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a : ℂ) + z))
    Differentiable ℂ Z ∧ ∀ l r : ℝ, l ≤ r → ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc l r → ‖Z z‖ ≤ C := by
  intro Z
  obtain ⟨hf, hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hd := globalThetaMellinIntegral_entire_of_vanishing f.val hf hf' χ
  refine ⟨hd.comp (show Differentiable ℂ (fun z : ℂ ↦ (a : ℂ) + z) by fun_prop), ?_⟩
  let u (x : C𝔽) := adelicTheta f.val x * (χ x : ℂ)
  let η : QuasiCharacter C𝔽 := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  have he (v : ℂ) (x : C𝔽) : adelicTheta f.val x * ideleClassNormTwist χ v x =
      u x * Complex.exp (v * (logNorm x : ℂ)) := by
    have hh := quasiCharacterNormTwist_eq_exp m𝔽 η v x
    change ideleClassNormTwist χ v x = (χ x : ℂ) * Complex.exp (v * (logNorm x : ℂ)) at hh
    rw [hh, ← mul_assoc]
  have hu (r : ℝ) : Integrable (fun x ↦ u x * Complex.exp ((r : ℂ) * (logNorm x : ℂ))) μ𝔽 :=
    (globalThetaMellinIntegral_integrable_of_vanishing f.val hf hf' _).congr (.of_forall (he r))
  intro l r _
  obtain ⟨C, hC⟩ := StripInterpolation.laplace_strip_bound μ𝔽 u logNorm hu (a + l) (a + r)
  refine ⟨C, fun z hz ↦ ?_⟩
  have hz' : ((a : ℂ) + z).re ∈ Icc (a + l) (a + r) := by
    change a + l ≤ a + z.re ∧ a + z.re ≤ a + r
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hv : Z z = ∫ x, u x * Complex.exp (((a : ℂ) + z) * (logNorm x : ℂ)) ∂μ𝔽 :=
    integral_congr_ae (.of_forall (he _))
  rw [hv]
  exact hC _ hz'

/-- On one compact-character chart every admitted jet has a Schwartz–Bergman
interpolant, vanishing at every remaining admitted jet on that entire chart. -/
private theorem stripProfile_single_chart (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (i : Jχ(χ, a, α, s)) (d : ℂ) :
    ∃ H : SchwartzBergman univ, ∀ j : Jχ(χ, a, α, s), j.val.1 = i.val.1 →
      iteratedDeriv dj(j) H.val Zj(j) = if j = i then d else 0 := by
  classical
  let n (j : Jχ(χ, a, α, s)) := multiplicity(χ j.val.1, shift(a + j.val.2.1, j.val.2.2.1))
  have hn (j : Jχ(χ, a, α, s)) : dj(j) < n j := by
    have hj := j.property
    change dj(j) < spectralStripMultiplicity α s j.val.2.1 (n j) at hj
    unfold spectralStripMultiplicity spectralBoundaryMultiplicity at hj
    split_ifs at hj <;> omega
  obtain ⟨f, hvan, hnon⟩ := i.exists_thetaMellin_first_nonvanishing
  let Z (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist (χ i.val.1) z)
  let W (z : ℂ) := Z ((a : ℂ) + z)
  have hv (j : Jχ(χ, a, α, s)) : (a : ℂ) + Zj(j) = shift(a + j.val.2.1, j.val.2.2.1) := by
    push_cast
    ring
  have ht (k : ℕ) (j : Jχ(χ, a, α, s)) :
      iteratedDeriv k W Zj(j) = iteratedDeriv k Z (shift(a + j.val.2.1, j.val.2.2.1)) := by
    exact (congrFun (iteratedDeriv_comp_const_add k Z (a : ℂ)) _).trans (congrArg (iteratedDeriv k Z) (hv j))
  obtain ⟨hd, hb⟩ := stripProfile_theta_strip_bound (χ i.val.1) f a
  have ho : analyticOrderAt W Zj(i) = n i := by
    apply (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hd.analyticAt _)).mpr
    exact ⟨fun k hk ↦ (ht k i).trans (hvan k hk), (ht _ i).trans_ne hnon⟩
  let c (k : Fin (n i)) := if (k : ℕ) = dj(i) then d else 0
  obtain ⟨H, hH, hother⟩ := StripInterpolation.interpolate_transform hd hb Zj(i) (n i) ho c
  refine ⟨H, fun j hω ↦ ?_⟩
  by_cases he : Zj(j) = Zj(i)
  · have hbj : j.val.2.1 = i.val.2.1 := by simpa using congrArg Complex.re he
    have htj : j.val.2.2.1 = i.val.2.2.1 := by simpa using congrArg Complex.im he
    have hnj : n j = n i := by simp only [n, hω, hbj, htj]
    have hij : j = i ↔ dj(j) = dj(i) :=
      ⟨fun e ↦ congrArg (fun x : Jχ(χ, a, α, s) ↦ dj(x)) e,
        fun h ↦ Subtype.ext (Prod.ext hω (Prod.ext hbj (Prod.ext htj h)))⟩
    rw [he]
    apply (hH ⟨dj(j), (hn j).trans_eq hnj⟩).trans
    by_cases e : j = i
    · simp [c, e]
    · simp [c, e, (not_congr hij).mp e]
  · rw [ite_eq_right (show j ≠ i from fun hj ↦ he (congrArg (fun x : Jχ(χ, a, α, s) ↦ Zj(x)) hj))]
    apply hother Zj(j) he (n j) _ dj(j) (hn j)
    intro k hk
    rw [ht k j]
    apply stripTheta_mellin_zero
    simpa only [n, hω] using hk

local notation "Ws(" α ", " s ")" => CompactIntervalSobolev volume id (-α) α s
local notation "finiteJetMoments(" χ ", " a ", " hα ", " hs ")" =>
  {y : W(-_, _, _) | (Function.support (fun j : Jχ(χ, a, _, _) ↦
    spectralSobolevPairing y ((stripU(χ, hα, hs)) j))).Finite}

/-- Every physical moment on the same chart is a scalar Mellin derivative. All
other compact characters have zero pairing. -/
private theorem stripTail_profile_pairing
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (ω : PontryaginDual C₁)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {I : Set ℝ} (hI : IsOpen I) (hsub : Icc (-α) α ⊆ I)
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hlog : MeasurePreserving logNorm ν volume)
    (p : PositiveRealExponentialDecay I) (y : W(-α, α, s))
    (hy : (y : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * p.val (logNorm x)) (j : Jχ(χ, a, α, s)) :
    spectralSobolevPairing y ((stripU(χ, hα, hs)) j) = if j.val.1 = ω then
      ((Measure.haarScalarFactor μ𝔽 ν : ℝ) : ℂ) *
        iteratedDeriv dj(j) (mellin (fun t ↦ p.val (Real.log t))) Zj(j) else 0 := by
  have habs : μ𝔽 ≪ L2μ'(-α, α, s) :=
    withDensity_absolutelyContinuous'
      (symmIntervalSobolevDensity_inv_continuous hα s).measurable.ennreal_ofReal.aemeasurable
      (.of_forall fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr
        (inv_pos.mpr (symmIntervalSobolevDensity_pos hα s (logNorm g))))
  let q (r : ℝ) := ((r : ℂ)^dj(j) * p.val r) * Complex.exp (Zj(j) * (r : ℂ))
  have hu : (((spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))) : C𝔽 → ℂ) =ᵐ[μ𝔽] stripJet(χ, j) :=
    habs.ae_le (MemLp.coeFn_toLp _)
  let v (x : C𝔽) := (χ ω x : ℂ)⁻¹ * (χ j.val.1 x : ℂ)
  have hpair : spectralSobolevPairing y ((spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))) =
      ∫ x, v x * q (logNorm x) ∂μ𝔽 := by
    refine (integral_congr_ae (hy.mul hu)).trans (integral_congr_ae (.of_forall fun x ↦ ?_))
    change ((χ ω x : ℂ)⁻¹ * p.val (logNorm x)) * stripJet(χ, j) x = v x * q (logNorm x)
    rw [stripProfile_jet]
    dsimp only [v, q]
    ring
  rw [hpair]
  by_cases hω : j.val.1 = ω
  · rw [ite_eq_left hω]
    have hv (x : C𝔽) : v x = 1 := by dsimp [v]; rw [hω, inv_mul_cancel₀ (Circle.coe_ne_zero _)]
    simp_rw [hv, one_mul]
    have hz : Zj(j).re ∈ I := by simpa using hsub (j.mem_strip_order_pos hα).1
    exact stripProfile_log_moment hI (hsub ⟨neg_nonpos.mpr hα, hα⟩) ν
      hlog p dj(j) Zj(j) hz
  · rw [ite_eq_right hω]
    have hk : ∃ k : C₁, χ ω k.val ≠ χ j.val.1 k.val := by
      by_contra! he
      apply hω
      rw [← hχ j.val.1, ← hχ ω]
      exact DFunLike.ext _ _ fun k ↦ (he k).symm
    obtain ⟨k, hk⟩ := hk
    apply stripProfile_orthogonality μ𝔽 (χ ω) (χ j.val.1) k.val hk (fun x ↦ q (logNorm x))
    intro x
    change q (Real.log ((ideleClassNorm F (k.val * x)).val : ℝ)) = q (logNorm x)
    rw [map_mul, k.property, one_mul]

/-- Paper: Theorem 10.2.2.1, p. 446. Each admitted strip jet has an ambient Sobolev
interpolant with all its other admitted moments zero.
Deviation: The proof divides a polar-free entire Mellin transform within the scalar
Schwartz–Bergman space and uses the strict Sobolev cutoff at the boundary. -/
theorem spectralStripJet_singleInterpolant (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (i : Jχ(χ, a, α, s)) :
    ∃ y : W(-α, α, s), ∀ j : Jχ(χ, a, α, s),
      spectralSobolevPairing y ((spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))) =
        if j = i then 1 else 0 := by
  classical
  let ν := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let c : ℝ := Measure.haarScalarFactor μ𝔽 ν
  have hc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by
    have hpos : 0 < c := by exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν
    exact hpos.ne')
  obtain ⟨H, hH⟩ := stripProfile_single_chart χ i (c : ℂ)⁻¹
  let M := positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty
  let p := M.symm H
  have hM : mellin (fun t ↦ p.val (Real.log t)) = H.val := by
    funext z
    exact (positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty p z
      (mem_univ _)).symm.trans (congrArg (fun u : SchwartzBergman univ ↦ u.val z) (M.apply_symm_apply H))
  obtain ⟨y, hy⟩ := stripProfile_sobolev (χ i.val.1) hα hs p
  refine ⟨y, fun j ↦ ?_⟩
  rw [stripTail_profile_pairing χ hχ i.val.1 hα hs isOpen_univ (subset_univ _)
    ν (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽) p y hy j]
  by_cases hω : j.val.1 = i.val.1
  · rw [ite_eq_left hω, hM, hH j hω]
    split_ifs <;> simp [c, hc]
  · have hj : j ≠ i := fun he ↦ hω (congrArg (fun u : Jχ(χ, a, α, s) ↦ u.val.1) he)
    rw [ite_eq_right hω, ite_eq_right hj]

section StripBlaschkeMultipliers

open Complex MeromorphicOn Metric Real
open scoped ComplexConjugate

private theorem positiveOrder_le_of_finite {u v : WithTop ℤ} (hv : v ≠ ⊤) (h : max 0 u ≤ v) :
    (u.untop₀.toNat : ℤ) ≤ v.untop₀ := by
  cases v with
  | top => contradiction
  | coe n =>
    cases u with
    | top => simp at h
    | coe m =>
      have hm : m ≤ n := by exact_mod_cast (le_trans (le_max_right _ _) h)
      have hn : (0 : ℤ) ≤ n := by exact_mod_cast (le_trans (le_max_left _ _) h)
      simp only [WithTop.untop₀_coe]
      omega

private theorem continuedCompletedHeckeL_order_at_two_nonpos (χ : PontryaginDual C𝔽) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) (2 : ℂ) ≤ 0 := by
  by_contra! h
  have hbad := completedHeckeL_continuation_zeros χ _ (continuedCompletedHeckeL_spec χ).1
    (continuedCompletedHeckeL_spec χ).2 (by norm_num : 0 < (2:ℂ).re) h
  norm_num at hbad

/-- The positive Hecke divisor in every vertical strip centered at real part 2
satisfies the Blaschke condition after conformal transport to the disk.
The test attaining the polar-free divisor minimum at the center is nonzero there. -/
private theorem continuedCompletedHeckeL_strip_blaschke (χ : PontryaginDual C𝔽) {k : ℝ} (hk : 0 < k) :
    Summable (fun w : {w : ℂ // |w.re - 2| < (π / 2) / k} ↦
      ((meromorphicOrderAt (continuedCompletedHeckeL χ) w.val).untop₀.toNat : ℝ) *
        (1 - ‖stripBlaschkeToDisk 2 k w‖)) := by
  let L := continuedCompletedHeckeL χ
  have h₂ : meromorphicOrderAt L (2 : ℂ) ≤ 0 := continuedCompletedHeckeL_order_at_two_nonpos χ
  obtain ⟨f, hf⟩ := (isLeast_globalThetaMellinIntegral_orders χ (2 : ℂ)).1
  let G (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
  have hG₂ : meromorphicOrderAt G 2 = 0 := hf.trans (max_eq_left h₂)
  obtain ⟨h₀,h₁⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hG : Differentiable ℂ G := globalThetaMellinIntegral_entire_of_vanishing f.val h₀ h₁ χ
  have hzero : G 2 ≠ 0 := (hG.analyticAt _).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp hG₂
  let a := (π / 2) / k
  have ha : 0 < a := div_pos (by positivity) hk
  obtain ⟨M, hM⟩ := (stripProfile_theta_strip_bound χ f 0).2 (2-a) (2+a) (by linarith)
  have hB (w : ℂ) (hw : |w.re - (2 : ℂ).re| < (π / 2) / k) : ‖G w‖ ≤ M := by
    have hw' : |w.re - 2| < a := by simpa [a] using hw
    have hwI : w.re ∈ Icc (2-a) (2+a) :=
      ⟨by linarith [(abs_lt.mp hw').1], by linarith [(abs_lt.mp hw').2]⟩
    simpa only [Complex.ofReal_zero, zero_add] using hM w hwI
  have hall := verticalStrip_divisor_blaschke (w₀ := 2) hk G (fun z _ ↦ hG.analyticAt z) hzero hB
  have hGmero : MeromorphicOn G univ := fun z _ ↦ (hG.analyticAt z).meromorphicAt
  have hGfin (w : ℂ) : meromorphicOrderAt G w ≠ ⊤ :=
    MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hGmero
      isPreconnected_univ (x := (2:ℂ)) (mem_univ _) (mem_univ w) (by simp [hG₂])
  let W := {w : ℂ // |w.re-2| < a}
  have hd (w : W) : 0 ≤ 1 - ‖stripBlaschkeToDisk 2 k w‖ := by
    have hx : |w.val.re - (2 : ℂ).re| < (π / 2) / k := by simpa [a] using w.property
    have hh := stripBlaschkeToDisk_mem hk hx
    exact sub_nonneg.mpr (show ‖stripBlaschkeToDisk 2 k w‖ < 1 by simpa [mem_ball] using hh).le
  apply Summable.of_nonneg_of_le (fun w ↦ mul_nonneg (Nat.cast_nonneg _) (hd w)) _ hall
  intro w
  refine mul_le_mul_of_nonneg_right ?_ (hd w)
  exact_mod_cast positiveOrder_le_of_finite (hGfin w)
    ((isLeast_globalThetaMellinIntegral_orders χ (w : ℂ)).2 ⟨f,rfl⟩)

/-- An arbitrary family of distinct Hecke zeros inside the outer strip gives
nonzero pairwise-distinct disk points and the summable multiplicity bound used
by the infinite Blaschke tail products. -/
private theorem continuedCompletedHeckeL_blaschke_family {ι : Type*} (χ : PontryaginDual C𝔽)
    {k : ℝ} (hk : 0 < k) (p : ι → ℂ) (hp : Injective p)
    (hW : ∀ i, |(p i).re - 2| < (π / 2) / k)
    (hZ : ∀ i, 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) (p i))
    (m : ι → ℕ) (hm : ∀ i, m i ≤ (meromorphicOrderAt (continuedCompletedHeckeL χ) (p i)).untop₀.toNat) :
    let z (i : ι) := stripBlaschkeToDisk 2 k (p i)
    Injective z ∧ (∀ i, z i ≠ 0) ∧ (∀ i, ‖z i‖ < 1) ∧
      Summable (fun i ↦ (m i : ℝ) * (1 - ‖z i‖)) := by
  intro z
  have hW' (i) : |(p i).re - (2 : ℂ).re| < (π / 2) / k := by simpa using hW i
  have hleft (i) : stripBlaschkeFromDisk 2 k (z i) = p i := stripBlaschkeFromDisk_toDisk hk (hW' i)
  have hnorm (i) : ‖z i‖ < 1 := by simpa [z, mem_ball] using stripBlaschkeToDisk_mem hk (hW' i)
  refine ⟨fun i j h ↦ hp ((hleft i).symm.trans ((congrArg (stripBlaschkeFromDisk 2 k) h).trans (hleft j))),
    fun i h ↦ ?_, hnorm, ?_⟩
  · have he : p i = 2 := (hleft i).symm.trans (by simp [h,stripBlaschkeFromDisk])
    exact (not_lt_of_ge (continuedCompletedHeckeL_order_at_two_nonpos χ)) (he ▸ hZ i)
  · let P (i : ι) : {w : ℂ // |w.re-2| < (π / 2) / k} := ⟨p i, hW i⟩
    have hinj : Injective P := fun x y h ↦ hp (congrArg Subtype.val h)
    have hs := (continuedCompletedHeckeL_strip_blaschke χ hk).comp_injective hinj
    apply Summable.of_nonneg_of_le (fun i ↦ mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hnorm i).le)) _ hs
    intro i
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hm i)) (sub_nonneg.mpr (hnorm i).le)

/-- On a neighborhood of a prescribed closed Hecke strip, contractive
analytic multipliers tend to one. Each multiplier has the full prescribed
zero orders away from a finite set of distinct points in that closed strip. -/
private theorem exists_hecke_strip_tail_multipliers {ι : Type*} (χ : PontryaginDual C𝔽)
    (a α : ℝ) (hα : 0 ≤ α) (p : ι → ℂ) (hp : Injective p)
    (hstrip : ∀ i, |(p i).re| ≤ α)
    (hz : ∀ i, 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) ((a : ℂ) + p i))
    (m : ι → ℕ) (hm : ∀ i, m i ≤ (meromorphicOrderAt (continuedCompletedHeckeL χ)
      ((a : ℂ) + p i)).untop₀.toNat) :
    ∃ B : Finset ι → ℂ → ℂ,
      (∀ S, AnalyticOnNhd ℂ (B S) {w | |w.re| < α+1}) ∧
      (∀ S w, |w.re| < α+1 → ‖B S w‖ ≤ 1) ∧
      (∀ w, |w.re| < α+1 → Tendsto (fun S ↦ B S w) atTop (𝓝 1)) ∧
      ∀ (S : Finset ι) i, i ∉ S → (m i : ℕ∞) ≤ analyticOrderAt (B S) (p i) := by
  let R := |a-2|+α+2
  have hR : 0 < R := by dsimp [R]; linarith [abs_nonneg (a-2)]
  let k := (Real.pi / 2) / R
  have hk : 0 < k := div_pos (by positivity) hR
  have hwidth : (Real.pi / 2) / k = R := by
    dsimp [k]
    field_simp [Real.pi_ne_zero]
  let A (w : ℂ) := (a : ℂ) + w
  have hwide (z : ℂ) (hz' : |z.re| < α+1) : |(A z).re - 2| < (Real.pi/2)/k := by
    rw [hwidth]
    change |((a : ℂ) + z).re - 2| < |a-2| + α + 2
    rw [Complex.add_re, Complex.ofReal_re, show a + z.re - 2 = (a-2) + z.re by ring]
    linarith [abs_add_le (a-2) z.re]
  have hpI (i) : |(p i).re| < α+1 := (hstrip i).trans_lt (lt_add_one _)
  let φ (w : ℂ) := stripBlaschkeToDisk 2 k (A w)
  have hmap (w : ℂ) (hw : |w.re| < α+1) : φ w ∈ ball 0 1 :=
    stripBlaschkeToDisk_mem hk (by simpa using hwide w hw)
  have hφ (w : ℂ) (hw : |w.re| < α+1) : AnalyticAt ℂ φ w :=
    (stripBlaschkeToDisk_analytic (w₀ := 2) (w := A w) hk (by simpa using hwide w hw)).comp
      (analyticAt_const.add analyticAt_id)
  have hi : Injective (A ∘ p) := fun x y h ↦ hp (add_left_cancel h)
  obtain ⟨_, hne, hlt, hsum⟩ := continuedCompletedHeckeL_blaschke_family χ hk
    (A ∘ p) hi (fun i ↦ hwide _ (hpI i)) hz m hm
  obtain ⟨D, hD, hbound, hlim, hord⟩ := Blaschke.exists_holomorphic_disk_tails (φ ∘ p) m hne hlt hsum
  refine ⟨fun S ↦ D S ∘ φ, fun S w hw ↦ (hD S _ (hmap w hw)).comp (hφ w hw),
    fun S w hw ↦ hbound S _ (mem_ball_zero_iff.mp (hmap w hw)),
    fun w hw ↦ hlim _ (mem_ball_zero_iff.mp (hmap w hw)), ?_⟩
  intro S i hi
  have hd := hD S _ (hmap (p i) (hpI i))
  apply natCast_le_analyticOrderAt_comp hd (hφ _ (hpI i))
  obtain ⟨v, hv, he⟩ := hord S i hi
  apply (natCast_le_analyticOrderAt hd).mpr
  exact ⟨v, hv, he⟩

/-- For each compact character there is a sequence of bounded analytic cutoffs
on the widened strip. Apart from a finite set of actual strip-jet indices, each
cutoff kills the indicated order and every lower derivative on this component. -/
private theorem exists_spectralStripJet_tail_multipliers
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽) (ξ : PontryaginDual (ideleClassNorm F).ker)
    (a α s : ℝ) (hα : 0 ≤ α) :
    ∃ B : ℕ → ℂ → ℂ,
      (∀ n, DifferentiableOn ℂ (B n) {w | |w.re| < α+1}) ∧
      (∀ n w, |w.re| < α+1 → ‖B n w‖ ≤ 1) ∧
      (∀ w, |w.re| < α+1 → Tendsto (fun n ↦ B n w) atTop (𝓝 1)) ∧
      ∀ n, ∃ S : Finset (SpectralStripJetIndex χ a α s), ∀ j ∉ S, j.val.1 = ξ →
        ((j.val.2.2.2 + 1 : ℕ) : ℕ∞) ≤
          analyticOrderAt (B n) ((j.val.2.1 : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I) := by
  classical
  let J := SpectralStripJetIndex χ a α s
  let p (j : J) := (j.val.2.1 : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I
  let D := {j : J // j.val.1 = ξ}
  let Z := range (fun j : D ↦ p j.val)
  let order (w : ℂ) := (meromorphicOrderAt (continuedCompletedHeckeL (χ ξ)) ((a : ℂ) + w)).untop₀.toNat
  have hpa (j : J) : (a : ℂ) + p j = ((a+j.val.2.1 : ℝ) : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I := by
    simp [p, add_assoc]
  have hpre (j : J) : (p j).re = j.val.2.1 := by simp [p]
  have hpim (j : J) : (p j).im = j.val.2.2.1 := by simp [p]
  have hinside (w : Z) : |w.val.re| ≤ α := by
    obtain ⟨z, hz⟩ := w.property
    rw [← hz, hpre]
    exact abs_le.mpr (SpectralStripJetIndex.mem_strip_order_pos hα z.val).1
  have hpositive (w : Z) : 0 < meromorphicOrderAt (continuedCompletedHeckeL (χ ξ)) ((a : ℂ) + w.val) := by
    obtain ⟨z, hz⟩ := w.property
    rw [← hz, hpa]
    simpa only [show χ z.val.val.1 = χ ξ from congrArg χ z.property] using
      (SpectralStripJetIndex.mem_strip_order_pos hα z.val).2
  have hdeg (j : J) (hj : j.val.1 = ξ) : j.val.2.2.2 < order (p j) := by
    have h := j.property
    change j.val.2.2.2 < spectralStripMultiplicity α s j.val.2.1 _ at h
    rw [spectralStripMultiplicity] at h
    dsimp only [order]
    rw [hpa, ← hj]
    split_ifs at h with h₁ h₂
    · exact h
    · exact ((lt_spectralBoundaryMultiplicity _ _ _).mp h).1
    · omega
  have hfiber (w : Z) : {j : J | j.val.1 = ξ ∧ p j = w.val}.Finite := by
    let tuples := (Finset.range (order w.val)).image (fun k ↦ (ξ, w.val.re, w.val.im, k))
    apply (tuples.finite_toSet.preimage (f := fun j : J ↦ j.val) Subtype.val_injective.injOn).subset
    rintro j ⟨hj, h⟩
    refine Finset.mem_image.mpr ⟨j.val.2.2.2, Finset.mem_range.mpr (h ▸ hdeg j hj), ?_⟩
    exact Prod.ext hj.symm (Prod.ext ((congrArg Complex.re h).symm.trans (hpre j))
      (Prod.ext ((congrArg Complex.im h).symm.trans (hpim j)) rfl))
  let : Countable J := spectralStripJet_countable χ a α s
  let : Countable Z := Set.countable_range _
  obtain ⟨B, hB, hb, hl, ho⟩ := exists_hecke_strip_tail_multipliers (χ ξ) a α hα (fun w : Z ↦ w.val)
    Subtype.val_injective hinside hpositive (fun w ↦ order w.val) (fun _ ↦ le_rfl)
  obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset Z))
  refine ⟨fun n ↦ B (u n), fun n ↦ (hB _).differentiableOn, fun n ↦ hb (u n),
    fun w hw ↦ (hl w hw).comp hu, ?_⟩
  intro n
  let E : Set J := ⋃ w ∈ u n, {j | j.val.1 = ξ ∧ p j = w.val}
  have hE : E.Finite := (u n).finite_toSet.biUnion (fun w _ ↦ hfiber w)
  refine ⟨hE.toFinset, ?_⟩
  intro j hj hξ
  let w : Z := ⟨p j, ⟨⟨j,hξ⟩,rfl⟩⟩
  have ho' : w ∉ u n := by
    intro h
    apply hj
    exact hE.mem_toFinset.mpr <| mem_iUnion₂.mpr ⟨w,h,hξ,rfl⟩
  exact (ENat.natCast_le_natCast.mpr (hdeg j hξ)).trans (ho (u n) w ho')

end StripBlaschkeMultipliers

/-- The whole radial Hilbert range in an arbitrary prescribed character is in the
closure of ambient vectors with finite jet support. -/
private theorem stripTail_radial_mem_closure
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (ω : PontryaginDual C₁)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I) (hsub : Icc (-α) α ⊆ I)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot]
    (b : ι → ℂ → ℂ) (hb : ∀ n, DifferentiableOn ℂ (b n) (Complex.re ⁻¹' I))
    (hc : ∀ n z, z.re ∈ I → ‖b n z‖ ≤ 1)
    (hl : ∀ z, z.re ∈ I → Tendsto (fun n ↦ b n z) l (𝓝 1))
    (hcut : ∀ n, ∃ S : Finset (Jχ(χ, a, α, s)), ∀ j ∉ S, j.val.1 = ω →
      ((dj(j) + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (b n) Zj(j))
    (L : Ws(α, s) →L[ℂ] W(-α, α, s))
    (hL : ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * f (logNorm x)) :
    ∀ f, L f ∈ closure finiteJetMoments(χ, a, hα, hs) := by
  obtain ⟨P, -, hP, hrep⟩ := scalarIntervalSobolev_dense (-α) α s (stripI(hα)) hs I hI hInt hsub
  have h0 := hsub (show (0 : ℝ) ∈ Icc (-α) α from ⟨neg_nonpos.mpr hα, hα⟩)
  intro f
  refine hP.induction_on f ?_ (fun p ↦ ?_)
  · exact isClosed_closure.preimage L.continuous
  obtain ⟨q, hq, he⟩ := StripMultiplier.scalar_approximation hI hInt ⟨0, h0⟩ b hb hc hl p
  have ht : Tendsto (fun n ↦ L (P (q n))) l (𝓝 (L (P p))) :=
    ((L.continuous.tendsto _).comp (P.continuous.tendsto _)).comp hq
  apply mem_closure_of_tendsto ht
  refine .of_forall fun n ↦ ?_
  obtain ⟨S, hS⟩ := hcut n
  apply S.finite_toSet.subset
  intro j hj
  by_contra hjs
  apply hj
  let ν := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hn := (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽).quasiMeasurePreserving.ae_eq_comp (hrep (q n))
  have hrep' : (L (P (q n)) : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * (q n).val (logNorm x) := by
    refine (hL _).trans ?_
    apply (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 ν).ae_eq
    filter_upwards [hn] with x hx using congrArg ((χ ω x : ℂ)⁻¹ * ·) hx
  change spectralSobolevPairing (L (P (q n))) ((stripU(χ, hα, hs)) j) = 0
  rw [stripTail_profile_pairing χ hχ ω hα hs hI hsub ν (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽) _ _ hrep' j]
  split_ifs with hω
  · have hz : Zj(j).re ∈ I := by simpa using hsub (j.mem_strip_order_pos hα).1
    rw [StripMultiplier.lower_jet_zero hI p (q n) (b n) (hb n) (he n) hInt Zj(j) hz
      (hS j hjs hω) (Nat.lt_succ_self _), mul_zero]
  · rfl

/-- The radial phase from the chosen base character lies in the same weighted L² space. -/
private theorem stripTail_twisted_radial (ξ : PontryaginDual C𝔽) (τ : ℝ≥0ˣ →ₜ* C𝔽)
    {α s : ℝ} (f : Ws(α, s)) :
    ∃ g : Ws(α, s), (g : ℝ → ℂ) =ᵐ[volume] fun r ↦ (ξ (τ (sobolevLogEquiv r)) : ℂ) * f r := by
  let η := volume.withDensity fun r ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s r)
  have hac : volume ≪ η := withDensity_absolutelyContinuous'
    (continuous_intervalSobolevDensity' (-α) α s).measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun r ↦ (ENNReal.ofReal_pos.mpr (intervalSobolevDensity_pos _ _ _ r)).ne')
  let w (r : ℝ) := (ξ (τ (sobolevLogEquiv r)) : ℂ)
  have hw : Continuous w := continuous_subtype_val.comp
    (ξ.continuous.comp (τ.continuous.comp sobolevLogEquiv.continuous))
  have hunit (r : ℝ) : ‖w r‖ = 1 := Circle.norm_coe (ξ (τ (sobolevLogEquiv r)))
  obtain ⟨M, hM⟩ := sobolev_unitary_mul η w hw.measurable hunit
  exact ⟨M f, hac.ae_eq (hM f)⟩

/-- On a split group, each physical compact-character tensor is one of the given
base-character lifts after a unitary radial phase correction. -/
private theorem stripTail_pure_realization
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ m𝔽)
    (κ : Measure C₁) [SFinite κ]
    (he : QuasiMeasurePreserving (fun p : C₁ × ℝ≥0ˣ ↦ (p.1 : C𝔽) * τ p.2) (κ.prod positiveRealHaar) μ𝔽)
    (f : Ws(α, s)) (ψ : PontryaginDual C₁) (v : Lp ℂ 2 κ) (hv : (v : C₁ → ℂ) =ᵐ[κ] fun k ↦ (ψ k : ℂ)) :
    ∃ (g : Ws(α, s)) (y : W(-α, α, s)),
      ((y : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ψ⁻¹ x : ℂ)⁻¹ * g (logNorm x)) ∧
      (fun p : C₁ × ℝ≥0ˣ ↦ y ((p.1 : C𝔽) * τ p.2)) =ᵐ[κ.prod positiveRealHaar]
        fun p ↦ f (Real.log (p.2.val : ℝ)) * v p.1 := by
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let ω := ψ⁻¹
  let ξ := χ ω
  obtain ⟨g, hg⟩ := stripTail_twisted_radial ξ τ (α := α) (s := s) f
  obtain ⟨L, hL⟩ := stripTail_radial_lift ξ hα hs
  let y := L g
  refine ⟨g, y, hL g, ?_⟩
  have hsplit := he.ae_eq_comp (hL g)
  have hr := sobolevLog_ae hg
  have hrad := (Measure.quasiMeasurePreserving_snd (μ := κ) (ν := positiveRealHaar)).ae hr
  have hchar := (Measure.quasiMeasurePreserving_fst (μ := κ) (ν := positiveRealHaar)).ae hv
  let e (p : C₁ × ℝ≥0ˣ) := (p.1 : C𝔽) * τ p.2
  have hlog (p : C₁ × ℝ≥0ˣ) : logNorm (e p) = Real.log (p.2.val : ℝ) := by
    change Real.log ((m𝔽 ((p.1 : C𝔽) * τ p.2)).val : ℝ) = _
    rw [map_mul, show m𝔽 (p.1 : C𝔽) = 1 from p.1.property, one_mul, hτ]
  have hrt (t : ℝ≥0ˣ) : sobolevLogEquiv (Real.log (t.val : ℝ)) = t := by
    obtain ⟨u, rfl⟩ := sobolevLogEquiv.surjective t
    rw [sobolevLogEquiv_log]
  have hξ (k : C₁) : ξ (k : C𝔽) = (ψ k)⁻¹ := DFunLike.congr_fun (hχ ω) k
  filter_upwards [hsplit, hrad, hchar] with p hp hpr hpk
  change y (e p) = (ξ (e p) : ℂ)⁻¹ * g (logNorm (e p)) at hp
  change y (e p) = f (Real.log (p.2.val : ℝ)) * v p.1
  change g (Real.log (p.2.val : ℝ)) = (ξ (τ (sobolevLogEquiv _)) : ℂ) * f _ at hpr
  change v p.1 = (ψ p.1 : ℂ) at hpk
  rw [hp, hlog, hpr, hpk]
  change ((ξ ((p.1 : C𝔽) * τ p.2) : ℂ)⁻¹ * ((ξ (τ _) : ℂ) * f _)) = _
  rw [hrt, map_mul, Circle.coe_mul, hξ, Circle.coe_inv, mul_inv_rev, inv_inv]
  field_simp

open scoped TensorProduct InnerProductSpace in
/-- The canonical weighted Hilbert tensor map reads elementary product representatives
with respect to Tamagawa measure. -/
private theorem stripTail_weighted_tensor (α s : ℝ) (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ m𝔽)
    (κ : Measure C₁) [κ.IsHaarMeasure] (hκ : κ univ = 1) :
    let e (p : C₁ × ℝ≥0ˣ) := (p.1 : C𝔽) * τ p.2
    let m := κ.prod positiveRealHaar
    ∃ U : W(-α, α, s) ≃L[ℂ] UniformSpace.Completion (Ws(α, s) ⊗[ℂ] Lp ℂ 2 κ),
      QuasiMeasurePreserving e m μ𝔽 ∧ ∀ (f : Ws(α, s)) (v : Lp ℂ 2 κ) (y : W(-α, α, s)),
        ((y : C𝔽 → ℂ) ∘ e =ᵐ[m] fun p ↦ f (Real.log (p.2.val : ℝ)) * v p.1) →
        U y = ↑(f ⊗ₜ[ℂ] v) := by
  intro e m
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let ν := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hemeas : Measurable e :=
    (measurable_subtype_coe.comp measurable_fst).mul (τ.continuous.measurable.comp measurable_snd)
  have he : MeasurePreserving e m ν :=
    ⟨hemeas, (canonicalModulatedHaar_eq_map_prod m𝔽 hm𝔽 τ hτ κ hκ).symm⟩
  have hqp : QuasiMeasurePreserving e m μ𝔽 :=
    ⟨hemeas.aemeasurable, by rw [he.map_eq]; exact Measure.absolutelyContinuous_isHaarMeasure ν μ𝔽⟩
  let ρ := intervalSobolevDensity (-α) α s
  let P := sobolevSplit_tensor m𝔽 hm𝔽 τ hτ κ hκ ρ (continuous_intervalSobolevDensity' _ _ _)
  let Tc := globalThetaAmbient_equiv_canonical (F := F) hm𝔽 (-α) α s
  refine ⟨Tc.choose.trans P.choose.toContinuousLinearEquiv, hqp, fun f v y hy ↦ ?_⟩
  exact P.choose_spec f v (Tc.choose y) ((hqp.ae_eq_comp (Tc.choose_spec y).1).trans hy)

open scoped TensorProduct InnerProductSpace in
/-- The inverse-base-character lifts of the full radial weighted Hilbert spaces are total
in the arithmetic weighted Sobolev space, for every Sobolev exponent. -/
private theorem stripTail_angular_total
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (V : Submodule ℂ W(-α, α, s)) (hV : IsClosed (V : Set W(-α, α, s)))
    (hforms : ∀ (ω : PontryaginDual C₁) (f : Ws(α, s)) (y : W(-α, α, s)),
      ((y : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * f (logNorm x)) → y ∈ V) :
    ∀ y, y ∈ V := by
  let : CompactSpace C₁ := isCompact_iff_compactSpace.mp (IsModulation.isCompact_ker (m := m𝔽) hm𝔽)
  let κ : Measure C₁ := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts C₁)
  let : IsProbabilityMeasure κ := ⟨Measure.haarMeasure_self⟩
  obtain ⟨τ, hτ⟩ := exists_section_of_surjective hm𝔽.1 hms𝔽
  obtain ⟨U, he, hU⟩ := stripTail_weighted_tensor (F := F) α s τ hτ κ Measure.haarMeasure_self
  obtain ⟨v, hv, hvc⟩ := dense_span_pontryaginDual_toLp κ
  refine mem_of_mem_tmul_dense_family (A := Ws(α, s)) (B := Lp ℂ 2 κ) U V hV v hv ?_
  intro f ψ
  let R := stripTail_pure_realization (F := F) χ hχ hα hs τ hτ κ he f ψ (v ψ) (hvc ψ)
  let g := R.choose
  let y := R.choose_spec.choose
  have hy : y ∈ V := hforms ψ⁻¹ g y R.choose_spec.choose_spec.1
  have ht := hU f (v ψ) y R.choose_spec.choose_spec.2
  exact ((congrArg U.symm ht.symm).trans (U.symm_apply_apply y)).symm ▸ hy

/-- Paper: Theorem 10.2.2.1, p. 446. Vectors with only finitely many nonzero
admitted Hecke jet moments are dense in the full weighted strip Sobolev space.
Deviation: In place of the finite-band argument on pp. 443 and 446, use bounded
Blaschke products on a wider strip. At a boundary zero, the index includes
only derivative orders satisfying the strict cutoff `2k + 1 < s` (F152). -/
theorem spectralStripJet_dense_finite_moment_support
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (a α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    Dense finiteJetMoments(χ, a, hα, hs) := by
  let I := {r : ℝ | |r| < α + 1}
  have hI : I = Ioo (-(α + 1)) (α + 1) := by
    ext x
    change |x| < α + 1 ↔ -(α + 1) < x ∧ x < α + 1
    exact abs_lt
  have hopen : IsOpen I := hI ▸ isOpen_Ioo
  have hint : OrdConnected I := hI ▸ ordConnected_Ioo
  have hsub : Icc (-α) α ⊆ I := fun _ hr ↦ (abs_le.mpr hr).trans_lt (by linarith)
  let J := Jχ(χ, a, α, s)
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (stripI(hα)) hs).exists.choose
  let u (j : J) := (stripU(χ, hα, hs)) j
  let Lb (j : J) := (T.symm (u j)).toLinearMap
  have hLb (j : J) (x : W(-α, α, s)) : Lb j x = spectralSobolevPairing x (u j) :=
    (spectralSobolevPairing_dual (stripI(hα)) hs (T.symm (u j)) x).2.trans
      (congrArg (spectralSobolevPairing x) (T.apply_symm_apply (u j)))
  obtain ⟨S, hS⟩ := exists_submodule_finite_moment_support Lb
  have hset : (S : Set W(-α, α, s)) = finiteJetMoments(χ, a, hα, hs) := by
    rw [hS]
    ext x
    change (support (fun j : J ↦ Lb j x)).Finite ↔
      (support (fun j : J ↦ spectralSobolevPairing x (u j))).Finite
    simp only [hLb]
  have hcl : (S.topologicalClosure : Set W(-α, α, s)) = closure finiteJetMoments(χ, a, hα, hs) := by
    rw [← hset]
    rfl
  intro f
  change f ∈ closure finiteJetMoments(χ, a, hα, hs)
  rw [← hcl]
  apply stripTail_angular_total χ hχ hα hs S.topologicalClosure S.isClosed_topologicalClosure _ f
  intro ω g y hrep
  obtain ⟨L, hL⟩ := stripTail_radial_lift (χ ω) hα hs
  have hy : y = L g := by
    apply Lp.ext
    exact (withDensity_absolutelyContinuous _ _).ae_le (hrep.trans (hL g).symm)
  rw [hy, show L g ∈ S.topologicalClosure ↔ L g ∈ closure finiteJetMoments(χ, a, hα, hs) from
    Set.ext_iff.mp hcl _]
  obtain ⟨B, hb, hc, hl, hcut⟩ := exists_spectralStripJet_tail_multipliers χ ω a α s hα
  exact stripTail_radial_mem_closure χ hχ ω hα hs hopen hint hsub B hb hc hl hcut L hL g

/-- Paper: Theorem 10.2.2.1, p. 446. The constructed single-jet interpolants
span the geometric quotient densely under the reverse common-kernel inclusion.
Deviation: The ambient approximation uses strip Blaschke products in place of
the finite-band argument on p. 443. The reverse inclusion is the remaining
geometric approximation in the strip norm. -/
theorem spectralStripJet_dense_quotient_of_reverse (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hker : ∀ x : W(-α, α, s), (∀ j : Jχ(χ, a, α, s), spectralSobolevPairing x ((stripU(χ, hα, hs)) j) = 0) →
      x ∈ Θ(a, stripI(hα), hs)) :
    let v (i : Jχ(χ, a, α, s)) := (spectralStripJet_singleInterpolant χ hχ hα hs i).choose
    Dense (Submodule.span ℂ (range fun i ↦ (Θ(a, stripI(hα), hs)).mkQ (v i)) :
      Set (spectralSobolevQuotient F a (stripI(hα)) hs)) := by
  intro v
  let J := Jχ(χ, a, α, s)
  let N := Θ(a, stripI(hα), hs)
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (stripI(hα)) hs).exists.choose
  let u (j : J) := (stripU(χ, hα, hs)) j
  let L (j : J) := (T.symm (u j)).toLinearMap
  have hL (j : J) (x : W(-α, α, s)) : L j x = spectralSobolevPairing x (u j) :=
    (spectralSobolevPairing_dual (stripI(hα)) hs (T.symm (u j)) x).2.trans
      (congrArg (spectralSobolevPairing x) (T.apply_symm_apply (u j)))
  apply dense_span_quotient_biorthogonal_of_finite_support N.mkQL N.mkQ_surjective v L
  · intro i j
    rw [hL]
    by_cases he : i = j
    · subst j
      simpa only [ite_true] using (spectralStripJet_singleInterpolant χ hχ hα hs i).choose_spec i
    · simpa only [ite_eq_right he, ite_eq_right (Ne.symm he)] using
        (spectralStripJet_singleInterpolant χ hχ hα hs i).choose_spec j
  · intro x hx
    exact (spectralSobolevQuotient_eq_zero a (stripI(hα)) hs x).mpr
      (hker x (fun j ↦ (hL j _).symm.trans (hx j)))
  · apply (spectralStripJet_dense_finite_moment_support χ hχ a α s hα hs).mono
    intro x hx
    change (support (fun j : J ↦ L j x)).Finite
    change (support (fun j : J ↦ spectralSobolevPairing x (u j))).Finite at hx
    simpa only [hL] using hx


end StripSingleJets

section
open Filter Function MeasureTheory Metric Set
open scoped Topology ENNReal SchwartzMap

section

/-- A uniformly rapidly decaying analytic function on an open vertical strip
gives a Schwartz–Bergman element with its original values throughout that strip. -/
private theorem stripBergman_of_exponential_bound (l r : ℝ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Complex.re ⁻¹' Ioo l r)) (C : ℝ) (_hC : 0 ≤ C)
    (hb : ∀ z : ℂ, z.re ∈ Ioo l r → ‖f z‖ ≤ C * Real.exp (-|z.im|)) :
    ∃ F : SchwartzBergman (Ioo l r), ∀ z : ℂ, z.re ∈ Ioo l r → F.val z = f z := by
  let U := Complex.re ⁻¹' Ioo l r
  refine ⟨⟨U.indicator f, fun z hz ↦ indicator_of_notMem hz _, ?_, ?_⟩,
    fun z hz ↦ indicator_of_mem (show z ∈ U from hz) _⟩
  · exact hf.differentiableOn.congr (fun z hz ↦ indicator_of_mem hz _)
  · intro a b _hab hab N
    let D := max |a| |b|
    refine ⟨(N.factorial : ℝ) * Real.exp D * C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z.re ∈ Icc a b := hz
    have hvr : |z.re| ≤ D := abs_le_max_abs_abs hz'.1 hz'.2
    have hnorm : ‖z‖ ≤ D + |z.im| := (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
    have hfac := (div_le_iff₀ (show 0 < (N.factorial : ℝ) by positivity)).mp
      (Real.pow_div_factorial_le_exp ‖z‖ (norm_nonneg z) N)
    have hpow : ‖z‖ ^ N ≤ ((N.factorial : ℝ) * Real.exp D) * Real.exp |z.im| := by
      rw [mul_assoc, ← Real.exp_add, mul_comm]
      exact hfac.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hnorm) (by positivity))
    change ‖z ^ N * U.indicator f z‖ ≤ _
    rw [indicator_of_mem (show z ∈ U from hab hz') _, norm_mul, norm_pow]
    calc
      _ ≤ (((N.factorial : ℝ) * Real.exp D) * Real.exp |z.im|) * (C * Real.exp (-|z.im|)) :=
        mul_le_mul hpow (hb _ (hab hz')) (norm_nonneg _) (by positivity)
      _ = _ := by rw [Real.exp_neg]; field_simp

/-- A bounded analytic multiplier preserves the Schwartz–Bergman test space
on a smaller strip on which the test function is defined. -/
private theorem stripBergman_bounded_mul {I J : Set ℝ} (h : J ⊆ I)
    (f : SchwartzBergman I) (P : ℂ → ℂ)
    (hP : AnalyticOnNhd ℂ P (Complex.re ⁻¹' J)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ z : ℂ, z.re ∈ J → ‖P z‖ ≤ C) :
    ∃ F : SchwartzBergman J, ∀ z : ℂ, z.re ∈ J → F.val z = P z * f.val z := by
  let U := Complex.re ⁻¹' J
  let g (z : ℂ) := P z * f.val z
  refine ⟨⟨U.indicator g, fun z hz ↦ indicator_of_notMem hz _, ?_, ?_⟩,
    fun z hz ↦ indicator_of_mem (show z ∈ U from hz) _⟩
  · exact (hP.differentiableOn.mul (f.property.2.1.mono (preimage_mono h))).congr (fun z hz ↦ indicator_of_mem hz _)
  · intro a b hab habJ N
    obtain ⟨D, hD⟩ := f.property.2.2 a b hab (habJ.trans h) N
    refine ⟨C * D, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hzm := habJ hz
    change ‖z ^ N * U.indicator g z‖ ≤ _
    rw [indicator_of_mem (show z ∈ U from hzm) _]
    change ‖z ^ N * (P z * f.val z)‖ ≤ _
    rw [mul_left_comm, norm_mul]
    exact mul_le_mul (hb z hzm) (hD ⟨z, hz, rfl⟩) (norm_nonneg _) hC

/-- A pointwise-convergent, uniformly bounded family of multipliers multiplies a
fixed Schwartz–Bergman test convergently in the full strip test topology. -/
private theorem stripBergman_tendsto_of_dominated {I : Set ℝ} (Y : SchwartzBergman I)
    (F : ℕ → SchwartzBergman I) (C : ℝ) (_hC : 0 ≤ C)
    (hdom : ∀ n (z : ℂ), z.re ∈ I → ‖(F n).val z - Y.val z‖ ≤ C * ‖Y.val z‖)
    (hcv : ∀ z : ℂ, z.re ∈ I → Tendsto (fun n ↦ (F n).val z) atTop (𝓝 (Y.val z))) :
    Tendsto F atTop (𝓝 Y) := by
  let P : I × ℕ → Seminorm ℂ (SchwartzBergman I) := fun i ↦ Seminorm.of
    (fun f : schwartzBergmanSubmodule I ↦ (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
    (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  have hP : WithSeminorms P := withGeneratingSeminorms_spec (schwartzBergmanSubmodule I) _
  apply (hP.tendsto_nhds F Y).mpr
  rintro ⟨a, N⟩ ε hε
  let z (t : ℝ) := (a.val : ℂ) + (t : ℂ) * Complex.I
  have hz (t : ℝ) : (z t).re ∈ I := by simp [z]
  let u (t : ℝ) := weightedVerticalTrace a.val N Y.val t
  let d (n : ℕ) (t : ℝ) := weightedVerticalTrace a.val N (F n - Y).val t
  have hu : MemLp u 2 volume := schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) N Y
  have hd (n : ℕ) : MemLp (d n) 2 volume := schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) N (F n - Y)
  have hdlim (t : ℝ) : Tendsto (fun n ↦ d n t) atTop (𝓝 0) := by
    have h := ((hcv _ (hz t)).sub_const (Y.val (z t))).const_mul ((z t) ^ N)
    change Tendsto (fun n ↦ z t ^ N * ((F n).val (z t) - Y.val (z t))) atTop (𝓝 0)
    simpa only [sub_self, mul_zero] using h
  have hdb (n : ℕ) (t : ℝ) : ‖d n t‖ ≤ C * ‖u t‖ := by
    change ‖z t ^ N * ((F n).val (z t) - Y.val (z t))‖ ≤ C * ‖(z t) ^ N * Y.val (z t)‖
    rw [norm_mul, norm_mul, mul_left_comm C]
    exact mul_le_mul_of_nonneg_left (hdom n _ (hz t)) (norm_nonneg _)
  have hint : Integrable (fun t ↦ C ^ 2 * ‖u t‖ ^ 2) volume :=
    (hu.integrable_norm_pow (by norm_num : 2 ≠ 0)).const_mul _
  have hsq : Tendsto (fun n ↦ ∫ t, ‖d n t‖ ^ 2) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := (volume : Measure ℝ))
      (F := fun n t ↦ ‖d n t‖ ^ 2) (f := fun _ ↦ (0 : ℝ)) (fun t ↦ C ^ 2 * ‖u t‖ ^ 2)
      (fun n ↦ (hd n).aestronglyMeasurable.norm.pow 2) hint
      (fun n ↦ .of_forall fun t ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hdb n t) 2)
      (.of_forall fun t ↦ by simpa using (hdlim t).norm.pow 2)
    simpa using hh
  have heq (n : ℕ) : P (a, N) (F n - Y) = (∫ t, ‖d n t‖ ^ 2) ^ ((2 : ℝ)⁻¹) := by
    change (eLpNorm (d n) 2 volume).toReal = _
    rw [toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num) (hd n).aestronglyMeasurable]
    simp
  have hpow : Tendsto (fun n ↦ P (a, N) (F n - Y)) atTop (𝓝 0) := by
    simp_rw [heq]
    simpa using (hsq.rpow_const (Or.inr (by norm_num : 0 ≤ (2 : ℝ)⁻¹)))
  exact (tendsto_order.mp hpow).2 ε hε

/-- Inside an arbitrary buffered strip, the tail times an entire test is the
Mellin transform of an exponential test approximated in the full test topology
by multiples of the chosen generator. The multipliers themselves are actual
inverse-Mellin exponential tests on the same buffered strip. -/
private theorem stripBergman_regularized_mellin_division (A k c r : ℝ)
    (hk : 0 < k) (hkc : k < c) (hr : 0 < r) (hwide : k * (|0 - A| + r) < Real.pi / 2)
    (hcr : c * r < Real.pi / 2) (G T Q N : ℂ → ℂ) (H : SchwartzBergman (univ : Set ℝ))
    (hT : AnalyticOnNhd ℂ T {w : ℂ | |w.re - A| < (Real.pi / 2) / k})
    (hQ : AnalyticOnNhd ℂ Q {w : ℂ | |w.re - A| < (Real.pi / 2) / k})
    (hN : AnalyticOnNhd ℂ N {w : ℂ | |w.re - A| < (Real.pi / 2) / k})
    (hQn : ∀ z : ℂ, |z.re - A| < (Real.pi / 2) / k → Q z ≠ 0)
    (M L : ℝ) (hL : 0 ≤ L)
    (htb : ∀ z : ℂ, |z.re - A| < (Real.pi / 2) / k → ‖T z‖ ≤ 1)
    (hqb : ∀ z : ℂ, |z.re - A| < (Real.pi / 2) / k → ‖Q z‖ ≤ M)
    (hnb : ∀ z : ℂ, |z.re - A| < (Real.pi / 2) / k → ‖N z‖ ≤ L)
    (heq : ∀ z : ℂ, |z.re - A| < (Real.pi / 2) / k → T z * H.val z = G z * (N z / Q z)) :
    let J := Ioo (-r) r
    ∃ y : PositiveRealExponentialDecay J,
      (∀ z : ℂ, z.re ∈ J → mellin (fun x ↦ y.val (Real.log x)) z = T z * H.val z) ∧
      ∃ k' v : ℕ → PositiveRealExponentialDecay J, Tendsto v atTop (𝓝 y) ∧
        ∀ n (z : ℂ), z.re ∈ J → mellin (fun x ↦ (v n).val (Real.log x)) z =
          G z * mellin (fun x ↦ (k' n).val (Real.log x)) z := by
  intro J
  let U := {w : ℂ | |w.re - A| < (Real.pi / 2) / k}
  have hsub : Complex.re ⁻¹' J ⊆ U := by
    intro z hz
    have hj : |z.re| < r := abs_lt.mpr hz
    have hb : |z.re - A| ≤ |z.re| + |0 - A| := by simpa using abs_sub z.re A
    apply (lt_div_iff₀ hk).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb hk.le, mul_lt_mul_of_pos_left hj hk]
  have hrad (z : ℂ) (hz : z.re ∈ J) : |z.re - 0| ≤ r := by simpa using (abs_lt.mpr hz).le
  have hc := hk.trans hkc
  let e (n : ℕ) : ℝ := 1 / (n + 1)
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  let V (n : ℕ) := stripReciprocalCutoff 0 c (e n)
  have hV (n : ℕ) : AnalyticOnNhd ℂ (V n) (Complex.re ⁻¹' J) := fun z _ ↦ stripReciprocalCutoff_analytic ..
  have hVb (n : ℕ) (z : ℂ) (hz : z.re ∈ J) : ‖V n z‖ ≤ 1 :=
    stripReciprocalCutoff_norm_le_one 0 c r (e n) hc hr.le hcr (he n).le z (hrad z hz)
  obtain ⟨Y, hY⟩ := stripBergman_bounded_mul (J := J) (subset_univ _) H T (hT.mono hsub) 1 zero_le_one
    (fun z hz ↦ htb z (hsub hz))
  choose VY hVY using fun n ↦ stripBergman_bounded_mul (J := J) subset_rfl Y (V n) (hV n) 1 zero_le_one (hVb n)
  have hconv : Tendsto VY atTop (𝓝 Y) := by
    apply stripBergman_tendsto_of_dominated Y VY 2 (by norm_num)
    · intro n z hz
      rw [hVY n z hz, ← sub_one_mul, norm_mul]
      have hb : ‖V n z - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith [hVb n z hz])
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    · intro z hz
      have ht := (stripReciprocalCutoff_tendsto_compact 0 c {z} isCompact_singleton).tendsto_at (mem_singleton z)
      have hn : Tendsto (fun n ↦ V n z) atTop (𝓝 1) := ht.comp tendsto_one_div_add_atTop_nhds_zero_nat
      simp_rw [hVY _ z hz]
      simpa using hn.mul_const (Y.val z)
  have hK (n : ℕ) : ∃ K : SchwartzBergman J, ∀ z : ℂ, z.re ∈ J → K.val z = (V n z / Q z) * N z := by
    obtain ⟨C, hC, hb⟩ := stripReciprocal_regularized_decay A 0 k c r (e n) hk hkc hr.le hwide hcr (he n)
      Q hQ hQn M hqb 1 zero_le_one
    refine stripBergman_of_exponential_bound (-r) r _ ((stripReciprocal_regularized_analytic A 0 k c (e n) Q hQ hQn
      |>.mono hsub).mul (hN.mono hsub)) (C * L) (mul_nonneg hC.le hL) ?_
    intro z hz
    rw [norm_mul]
    have h₁ := hb z (hrad z hz)
    calc
      _ ≤ (C * Real.exp (-1 * |z.im|)) * L := mul_le_mul h₁ (hnb z (hsub hz)) (norm_nonneg _) (by positivity)
      _ = _ := by rw [neg_one_mul]; ring
  choose K hK' using hK
  have hne : J.Nonempty := nonempty_Ioo.mpr (by linarith)
  let M' := positiveRealFourierMellin J isOpen_Ioo (ordConnected_Ioo) hne
  have hM' (F : SchwartzBergman J) (z : ℂ) (hz : z.re ∈ J) :
      mellin (fun x ↦ (M'.symm F).val (Real.log x)) z = F.val z := by
    rw [← positiveRealFourierMellin_apply J isOpen_Ioo (ordConnected_Ioo) hne _ z hz]
    exact congrArg (fun v : SchwartzBergman J ↦ v.val z) (M'.apply_symm_apply F)
  refine ⟨M'.symm Y, fun z hz ↦ (hM' _ _ hz).trans (hY z hz), fun n ↦ M'.symm (K n),
    fun n ↦ M'.symm (VY n), (M'.symm.continuous.tendsto Y).comp hconv, ?_⟩
  intro n z hz
  rw [hM' _ _ hz, hM' _ _ hz, hVY n z hz, hY z hz, heq z (hsub hz), hK' n z hz]
  ring

/-- The normalized complementary tail of the actual zeros of one strip generator
takes any entire test killing the finitely many excluded multiplicities to the
closure, in the exponential test topology, of products by that generator. -/
private theorem stripBergman_single_generator_finite_jets (A k c r : ℝ)
    (hk : 0 < k) (hkc : k < c) (hr : 0 < r) (hwide : k * (|0 - A| + r) < Real.pi / 2)
    (hcr : c * r < Real.pi / 2) (G : ℂ → ℂ)
    (hG : AnalyticOnNhd ℂ G {w : ℂ | |w.re - A| < (Real.pi / 2) / k})
    (hG₀ : G (A : ℂ) ≠ 0) (M : ℝ) (hb : ∀ z : ℂ, |z.re - A| < (Real.pi / 2) / k → ‖G z‖ ≤ M) :
    let D := stripBlaschkeFromDisk (A : ℂ) k
    let B := stripBlaschkeToDisk (A : ℂ) k
    let Z := {z : ℂ // z ∈ ball 0 1 ∧ G (D z) = 0}
    let a (i : Z) := i.val
    let m (i : Z) := analyticOrderNatAt G (D i.val)
    let J := Ioo (-r) r
    ∀ (S : Finset Z) (H : SchwartzBergman (univ : Set ℝ)),
      (∀ i ∈ S, (m i : ℕ∞) ≤ analyticOrderAt H.val (D i.val)) →
      ∃ y : PositiveRealExponentialDecay J,
        (∀ z : ℂ, z.re ∈ J → mellin (fun x ↦ y.val (Real.log x)) z = Blaschke.tail a m S (B z) * H.val z) ∧
        ∃ K v : ℕ → PositiveRealExponentialDecay J, Tendsto v atTop (𝓝 y) ∧
          ∀ n (z : ℂ), z.re ∈ J → mellin (fun x ↦ (v n).val (Real.log x)) z =
            G z * mellin (fun x ↦ (K n).val (Real.log x)) z := by
  intro D B Z a m J S H hHjets
  let U := {w : ℂ | |w.re - A| < (Real.pi / 2) / k}
  let Gd := G ∘ D
  let Hd := H.val ∘ D
  have hD (z : ℂ) (hz : z ∈ ball 0 1) : D z ∈ U := stripBlaschkeFromDisk_mem_strip hk hz
  have hB (z : ℂ) (hz : z ∈ U) : B z ∈ ball 0 1 := stripBlaschkeToDisk_mem hk hz
  have hBa (z : ℂ) (hz : z ∈ U) : AnalyticAt ℂ B z := stripBlaschkeToDisk_analytic hk hz
  have hlog (z : ℂ) (hz : z ∈ U) : D (B z) = z := stripBlaschkeFromDisk_toDisk hk hz
  have hDa (z : ℂ) (hz : z ∈ ball 0 1) : AnalyticAt ℂ D z :=
    (stripBlaschkeFromDisk_analyticAt_deriv_ne_zero hk hz).1
  have hGd : AnalyticOnNhd ℂ Gd (ball 0 1) := fun z hz ↦ (hG _ (hD z hz)).comp (hDa z hz)
  have hHent : AnalyticOnNhd ℂ H.val univ :=
    (show DifferentiableOn ℂ H.val univ by simpa only [preimage_univ] using H.property.2.1).analyticOnNhd isOpen_univ
  have hHd : AnalyticOnNhd ℂ Hd (ball 0 1) := fun z hz ↦ (hHent _ (mem_univ _)).comp (hDa z hz)
  have h₀ : Gd 0 ≠ 0 := by simpa [Gd, D, stripBlaschkeFromDisk] using hG₀
  have ha (i : Z) : a i ≠ 0 := by
    intro ha
    have hi : Gd (a i) = 0 := i.property.2
    exact h₀ (ha ▸ hi)
  have ha' (i : Z) : ‖a i‖ < 1 := mem_ball_zero_iff.mp i.property.1
  obtain ⟨horder, hsum⟩ := stripBlaschke_disk_zero_orders hk G hG hG₀ hb
  obtain ⟨Q, hQ, hn, hQb, hdiv⟩ := Blaschke.exists_tail_test_quotient a m Subtype.val_injective ha ha'
    hsum Gd hGd (fun i ↦ (horder i).2.2) (fun z hz he ↦ ⟨⟨z, hz, he⟩, rfl⟩) M (fun z hz ↦ hb _ (hD z hz))
  let R := (Real.pi / 2) / k
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨L, hLb⟩ := H.property.2.2 (A - R) (A + R) (by linarith) (subset_univ _) 0
  have hHdBound (z : ℂ) (hz : z ∈ ball 0 1) : ‖Hd z‖ ≤ L := by
    have hz' : |(D z).re - A| < R := hD z hz
    have hwin : (D z).re ∈ Icc (A - R) (A + R) := ⟨by linarith [(abs_lt.mp hz').1], by linarith [(abs_lt.mp hz').2]⟩
    simpa [Hd] using hLb ⟨D z, hwin, rfl⟩
  have hj (i) (hi : i ∈ S) : (m i : ℕ∞) ≤ analyticOrderAt Hd (a i) := by
    have h := stripBlaschkeFromDisk_analyticAt_deriv_ne_zero (w₀ := (A : ℂ)) hk i.property.1
    change _ ≤ analyticOrderAt (H.val ∘ D) i.val
    rw [analyticOrderAt_comp_of_deriv_ne_zero h.1 h.2]
    exact hHjets i hi
  obtain ⟨N, hN, hNb, hrel⟩ := hdiv S Hd hHd hj L hHdBound
  let T := Blaschke.tail a m S
  have hTa : AnalyticOnNhd ℂ T (ball 0 1) := Blaschke.analyticOnNhd_tail a m S ha ha' hsum
  have hTb (z : ℂ) (hz : z ∈ ball 0 1) : ‖T z‖ ≤ 1 :=
    Blaschke.norm_tail_le_one a m S ha ha' hsum (mem_ball_zero_iff.mp hz)
  apply stripBergman_regularized_mellin_division A k c r hk hkc hr hwide hcr G (T ∘ B) (Q ∘ B) (N ∘ B) H
    (fun z hz ↦ (hTa _ (hB z hz)).comp (hBa z hz)) (fun z hz ↦ (hQ _ (hB z hz)).comp (hBa z hz))
    (fun z hz ↦ (hN _ (hB z hz)).comp (hBa z hz)) (fun z hz ↦ hn _ (hB z hz))
    M L ((norm_nonneg _).trans (hHdBound 0 (by simp))) (fun z hz ↦ hTb _ (hB z hz))
    (fun z hz ↦ hQb _ (hB z hz)) (fun z hz ↦ hNb _ (hB z hz))
  intro z hz
  simpa only [T, Hd, Gd, Function.comp_apply, hlog z hz] using hrel _ (hB z hz)

end

end

section

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

section

namespace SharpStripEval

private theorem polynomial_le_exp {s d : ℝ} (hs : 0 ≤ s) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, (1 + x ^ 2) ^ (s / 2) ≤ C * Real.exp (d * |x|) := by
  let r := d / (s + 1)
  let A := max 1 (1 / r)
  have hsp : 0 < s + 1 := by linarith
  have hr : 0 < r := div_pos hd hsp
  have hA : 1 ≤ A := le_max_left _ _
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hAr : 1 ≤ A * r := (div_le_iff₀ hr).mp (le_max_right _ _)
  have hrs : r * s ≤ d := by
    have hh : r * (s + 1) = d := div_mul_cancel₀ _ hsp.ne'
    nlinarith
  refine ⟨A ^ s, Real.rpow_pos_of_pos hA0 _, fun x ↦ ?_⟩
  have hx := abs_nonneg x
  have he : 1 + |x| ≤ A * Real.exp (r * |x|) := calc
    _ ≤ A + (A * r) * |x| := add_le_add hA (le_mul_of_one_le_left hx hAr)
    _ = A * (r * |x| + 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hA0.le
  calc
    _ ≤ ((1 + |x|) ^ 2) ^ (s / 2) :=
      Real.rpow_le_rpow (by positivity) (by nlinarith [sq_abs x]) (by linarith)
    _ = (1 + |x|) ^ s := by
      rw [← Real.rpow_natCast (1 + |x|) 2, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      ring
    _ ≤ (A * Real.exp (r * |x|)) ^ s := Real.rpow_le_rpow (by positivity) he hs
    _ = A ^ s * Real.exp ((r * s) * |x|) := by
      rw [Real.mul_rpow hA0.le (Real.exp_pos _).le, ← Real.exp_mul]
      ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrs hx))
      (Real.rpow_nonneg hA0.le _)

/-- Any strict increase in strip width absorbs every nonnegative polynomial Sobolev degree. -/
private theorem exists_id_on_wider_strip {α β s t : ℝ} (hα : 0 ≤ α) (hαβ : α < β)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∃ J : CompactIntervalSobolev volume id (-β) β t →L[ℂ]
        CompactIntervalSobolev volume id (-α) α s,
      ∀ f, (J f : ℝ → ℂ) =ᵐ[volume] (f : ℝ → ℂ) := by
  let D (a p : ℝ) := intervalSobolevDensity (-a) a p
  let ν (a p : ℝ) := volume.withDensity (fun x ↦ ENNReal.ofReal (D a p x))
  obtain ⟨C, hC, hpow⟩ := polynomial_le_exp hs (by linarith : 0 < 2 * (β - α))
  have hD (x : ℝ) : D α s x ≤ C * D β t x := by
    change intervalSobolevDensity (-α) α s x ≤ C * intervalSobolevDensity (-β) β t x
    rw [symmIntervalSobolevDensity_eq hα, symmIntervalSobolevDensity_eq (hα.trans hαβ.le)]
    have ht1 : (1 : ℝ) ≤ (1 + x ^ 2) ^ (t / 2) :=
      Real.one_le_rpow (by linarith [sq_nonneg x]) (by linarith)
    calc
      _ ≤ Real.exp (2 * α * |x|) * (C * Real.exp (2 * (β - α) * |x|)) :=
        mul_le_mul_of_nonneg_left (hpow x) (Real.exp_pos _).le
      _ = C * Real.exp (2 * β * |x|) := by
        rw [mul_left_comm, ← Real.exp_add]
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (Real.exp_pos _).le ht1) hC.le
  have hle : ν α s ≤ ENNReal.ofReal C • ν β t := by
    dsimp only [ν]
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    apply withDensity_mono (.of_forall fun x ↦ ?_)
    change ENNReal.ofReal (D α s x) ≤ ENNReal.ofReal C * ENNReal.ofReal (D β t x)
    rw [← ENNReal.ofReal_mul hC.le]
    exact ENNReal.ofReal_le_ofReal (hD x)
  have hac := Measure.absolutelyContinuous_of_le_smul hle
  let L := Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) ENNReal.ofReal_ne_top hle
  have hL (f : Lp ℂ 2 (ν β t)) : (L f : ℝ → ℂ) =ᵐ[ν α s] (f : ℝ → ℂ) :=
    Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hle f
  let J : Lp ℂ 2 (ν β t) →L[ℂ] Lp ℂ 2 (ν α s) :=
    { toFun := L
      map_add' := L.map_add
      map_smul' := fun c f ↦ Lp.ext ((hL (c • f)).trans ((hac.ae_eq (Lp.coeFn_smul c f)).trans
        (((hL f).symm.fun_comp (c • ·)).trans (Lp.coeFn_smul c (L f)).symm)))
      cont := L.continuous }
  have hm : Measurable (D α s) := by unfold D intervalSobolevDensity; fun_prop
  have hp (x : ℝ) : 0 < D α s x := by
    change 0 < intervalSobolevDensity (-α) α s x
    rw [symmIntervalSobolevDensity_eq hα]
    positivity
  have hbase : volume ≪ ν α s := withDensity_absolutelyContinuous'
    hm.ennreal_ofReal.aemeasurable (.of_forall fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr (hp x))
  exact ⟨J, fun f ↦ hbase.ae_eq (hL f)⟩

/-- Paper: Theorem 10.2.2.1, p. 446.
On entire exponential tests the order-`k` Mellin derivative extends continuously to the
symmetric scalar Sobolev space exactly in the interior, or at an endpoint with
`2 * k + 1 < s`.
Deviation: The strict boundary inequality is the correction F152. Necessity outside the strip
follows by embedding a wider interval with degree zero and applying its endpoint criterion. -/
private theorem scalarIntervalSobolev_eval_iff (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (k : ℕ) (z : ℂ) :
    (∃ Λ : CompactIntervalSobolev volume id (-α) α s →L[ℂ] ℂ,
      ∀ (f : PositiveRealExponentialDecay univ) (u : CompactIntervalSobolev volume id (-α) α s),
        (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) ↔
      |z.re| < α ∨ |z.re| = α ∧ 2 * (k : ℝ) + 1 < s := by
  let β := |z.re|
  have hβ : 0 ≤ β := abs_nonneg _
  have hmem : z.re ∈ ({-β, β} : Set ℝ) := by
    by_cases hz : 0 ≤ z.re
    · exact Or.inr (by simp [β, abs_of_nonneg hz])
    · exact Or.inl (by simp [β, abs_of_nonpos (le_of_not_ge hz)])
  have eint (p : ℝ) (hp : 0 ≤ p) := scalarIntervalSobolev_eval_boundary_iff (-β) β p
    ((neg_nonpos.mpr hβ).trans hβ) hp k z hmem
  rcases lt_trichotomy β α with h | he | h
  · refine ⟨fun _ ↦ Or.inl h, fun _ ↦ ?_⟩
    let p : ℝ := 2 * k + 2
    obtain ⟨Λ, hΛ⟩ := (eint p (by dsimp [p]; positivity)).mpr (by dsimp [p]; linarith)
    obtain ⟨J, hJ⟩ := exists_id_on_wider_strip hβ h (s := p) (t := s) (by dsimp [p]; positivity) hs
    exact ⟨Λ.comp J, fun f u hu ↦ hΛ f (J u) ((hJ u).trans hu)⟩
  · subst α
    constructor
    · intro hbounded
      exact Or.inr ⟨rfl, (eint s hs).mp hbounded⟩
    · rintro (hlt | ⟨_, horder⟩)
      · exact (lt_irrefl _ hlt).elim
      · exact (eint s hs).mpr horder
  · refine ⟨?_, fun hc ↦ False.elim ?_⟩
    · rintro ⟨Λ, hΛ⟩
      obtain ⟨J, hJ⟩ := exists_id_on_wider_strip hα h hs (show (0 : ℝ) ≤ 0 from le_rfl)
      have hi := (eint 0 le_rfl).mp ⟨Λ.comp J, fun f u hu ↦ hΛ f (J u) ((hJ u).trans hu)⟩
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith
    · rcases hc with hh | ⟨hh, _⟩ <;> change α < |z.re| at h <;> linarith

end SharpStripEval

end

end

section

open Filter Function MeasureTheory Set
open scoped SchwartzMap FourierTransform Topology ENNReal

namespace StripMultiplier

private def reflectedTwist {I : Set ℝ} (a : I) (p : PositiveRealExponentialDecay I) : 𝓢(ℝ, ℂ) :=
  schwartzChangeVariable ℂ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv
    (logExponentialDecayTwist I a p)

private theorem mellin_eq_fourier_twist {I : Set ℝ} (a : I) (p : PositiveRealExponentialDecay I)
    (u : ℝ) :
    mellin (fun t ↦ p.val (Real.log t)) ⟨a.val, u * (2 * Real.pi)⟩ = 𝓕 (reflectedTwist a p) u := by
  rw [SchwartzMap.fourier_coe, mellin_eq_fourier]
  rw [mul_div_cancel_right₀ _ (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
  apply congrArg (fun g : ℝ → ℂ ↦ 𝓕 g u)
  funext x
  change _ = logExponentialDecayTwist I a p (-x)
  rw [logExponentialDecayTwist_apply I a p (-x), Real.log_exp, Complex.real_smul, neg_mul, mul_neg]

private theorem norm_twist_sq {I : Set ℝ} (a : I) (p : PositiveRealExponentialDecay I) (x : ℝ) :
    ‖logExponentialDecayTwist I a p x‖ ^ 2 = Real.exp (2 * a.val * x) * ‖p.val x‖ ^ 2 := by
  rw [logExponentialDecayTwist_apply I a p x, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

private theorem reflected_integral {I : Set ℝ} (a : I) (p : PositiveRealExponentialDecay I) :
    ∫ x, ‖reflectedTwist a p x‖ ^ 2 = ∫ x, Real.exp (2 * a.val * x) * ‖p.val x‖ ^ 2 := by
  change ∫ x, ‖logExponentialDecayTwist I a p (-x)‖ ^ 2 = _
  rw [integral_neg_eq_self (fun x ↦ ‖logExponentialDecayTwist I a p x‖ ^ 2)]
  exact integral_congr_ae (Eventually.of_forall (norm_twist_sq a p))

/-- A multiplier contractive on one vertical Mellin line is contractive for the
corresponding exponential square norm of logarithmic test profiles. -/
private theorem line_contraction {I : Set ℝ} (a : I) (p q : PositiveRealExponentialDecay I)
    (h : ∀ v : ℝ, ‖mellin (fun t ↦ q.val (Real.log t)) ⟨a.val, v⟩‖ ≤
      ‖mellin (fun t ↦ p.val (Real.log t)) ⟨a.val, v⟩‖) :
    ∫ x, Real.exp (2 * a.val * x) * ‖q.val x‖ ^ 2 ≤
      ∫ x, Real.exp (2 * a.val * x) * ‖p.val x‖ ^ 2 := by
  rw [← reflected_integral, ← reflected_integral, ← SchwartzMap.integral_norm_sq_fourier,
    ← SchwartzMap.integral_norm_sq_fourier (reflectedTwist a p)]
  apply integral_mono
  · exact ((𝓕 (reflectedTwist a q)).memLp 2 volume).integrable_norm_pow (by norm_num : 2 ≠ 0)
  · exact ((𝓕 (reflectedTwist a p)).memLp 2 volume).integrable_norm_pow (by norm_num : 2 ≠ 0)
  · intro u
    have hu := h (u * (2 * Real.pi))
    rw [mellin_eq_fourier_twist, mellin_eq_fourier_twist] at hu
    exact pow_le_pow_left₀ (norm_nonneg _) hu 2

/-- A uniform bound for translates of a nonnegative window passes to every
positive mixture of those windows. -/
private theorem integrate_window_bounds {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    (μ : Measure X) (ν : Measure U) [SFinite μ] [SFinite ν]
    (K : U → X → ℝ≥0∞) (hK : Measurable (uncurry K)) (f g : X → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (C : ℝ≥0∞)
    (h : ∀ u, ∫⁻ x, K u x * g x ∂μ ≤ C * ∫⁻ x, K u x * f x ∂μ) :
    ∫⁻ x, (∫⁻ u, K u x ∂ν) * g x ∂μ ≤ C * ∫⁻ x, (∫⁻ u, K u x ∂ν) * f x ∂μ := by
  have swap (F : X → ℝ≥0∞) (hF : Measurable F) :
      ∫⁻ x, (∫⁻ u, K u x ∂ν) * F x ∂μ = ∫⁻ u, ∫⁻ x, K u x * F x ∂μ ∂ν := by
    calc
      _ = ∫⁻ x, ∫⁻ u, K u x * F x ∂ν ∂μ := by
        apply lintegral_congr
        intro x
        exact (lintegral_mul_const _ (hK.comp (measurable_id.prodMk measurable_const))).symm
      _ = _ := lintegral_lintegral_swap ((hK.comp measurable_swap).mul (hF.comp measurable_fst)).aemeasurable
  rw [swap g hg, swap f hf]
  calc
    _ ≤ ∫⁻ u, C * ∫⁻ x, K u x * f x ∂μ ∂ν := lintegral_mono h
    _ = _ := lintegral_const_mul _ ((hK.mul (hf.comp measurable_snd)).lintegral_prod_right')

/-- The smooth step is temperate. Every derivative of positive order vanishes
outside the unit interval. -/
private theorem smoothTransition_temperate : Function.HasTemperateGrowth Real.smoothTransition := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  have hcompact : HasCompactSupport (fderiv ℝ Real.smoothTransition) := by
    apply hasCompactSupport_norm_iff.mp
    simpa only [← norm_deriv_eq_norm_fderiv] using Real.smoothTransition.hasCompactSupport_deriv.norm
  apply Function.HasTemperateGrowth.of_fderiv (hcompact.hasTemperateGrowth (hc.fderiv_right (by simp)))
    (hc.differentiable (by simp)) (C := 1) (k := 0)
  intro x
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)] using Real.smoothTransition.le_one x

private def multiplyProfile {I : Set ℝ} (g : ℝ → ℂ) (hg : g.HasTemperateGrowth)
    (p : PositiveRealExponentialDecay I) : PositiveRealExponentialDecay I := by
  refine ⟨fun x ↦ g x * p.val x, (Submodule.mem_iInf _).2 ?_⟩
  intro a
  refine ⟨SchwartzMap.smulLeftCLM ℂ g (logExponentialDecayTwist I a p), ?_⟩
  funext x
  change SchwartzMap.smulLeftCLM ℂ g (logExponentialDecayTwist I a p) x =
    (Real.exp (a.val * x) : ℂ) * (g x * p.val x)
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, logExponentialDecayTwist_apply I a p x, smul_eq_mul]
  ring

private def window (β u x : ℝ) : ℝ := Real.exp (-(2 * β) * |x - u|)

private theorem window_le_line (β u x : ℝ) (hβ : 0 ≤ β) :
    window β u x ≤ Real.exp (2 * β * (x - u)) ∧ window β u x ≤ Real.exp (-(2 * β) * (x - u)) := by
  unfold window
  constructor <;> apply Real.exp_le_exp.mpr
  · nlinarith [mul_nonneg hβ (show 0 ≤ |x - u| + (x - u) from by linarith [neg_abs_le (x - u)])]
  · nlinarith [mul_nonneg hβ (sub_nonneg.mpr (le_abs_self (x - u)))]

private theorem line_step_bounds (β y : ℝ) (hβ : 0 ≤ β) :
    Real.exp (-(2 * β) * y) * Real.smoothTransition y ^ 2 ≤ window β 0 y ∧
    Real.exp (2 * β * y) * (1 - Real.smoothTransition y) ^ 2 ≤ Real.exp (4 * β) * window β 0 y := by
  have h0 := Real.smoothTransition.nonneg y
  have h1 := Real.smoothTransition.le_one y
  have hpow : Real.smoothTransition y ^ 2 ≤ 1 := by nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have hpow' : (1 - Real.smoothTransition y) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0 ≤ 2 - Real.smoothTransition y by linarith)]
  simp only [window, sub_zero]
  constructor
  · by_cases hy : y ≤ 0
    · simp [Real.smoothTransition.zero_of_nonpos hy, (Real.exp_pos _).le]
    · rw [abs_of_nonneg (le_of_not_ge hy)]
      exact (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le).trans_eq (mul_one _)
  · by_cases hy : 1 ≤ y
    · simp only [Real.smoothTransition.one_of_one_le hy, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
      positivity
    · calc
        _ ≤ Real.exp (2 * β * y) := (mul_le_mul_of_nonneg_left hpow' (Real.exp_pos _).le).trans_eq (mul_one _)
        _ ≤ _ := by
          rw [← Real.exp_add, Real.exp_le_exp]
          by_cases h : 0 ≤ y
          · rw [abs_of_nonneg h]
            nlinarith [mul_nonneg hβ (sub_nonneg.mpr (le_of_not_ge hy))]
          · rw [abs_of_nonpos (le_of_not_ge h)]
            nlinarith

private def lineWeight (v u x : ℝ) : ℝ := Real.exp (2 * v * (x - u))

private def energy {I : Set ℝ} (w : ℝ → ℝ) (p : PositiveRealExponentialDecay I) : ℝ :=
  ∫ x, w x * ‖p.val x‖ ^ 2

private theorem profile_continuous {I : Set ℝ} (h0 : 0 ∈ I) (p : PositiveRealExponentialDecay I) :
    Continuous p.val := by
  apply (logExponentialDecayTwist I ⟨0, h0⟩ p).continuous.congr
  intro x
  simpa using logExponentialDecayTwist_apply I ⟨0, h0⟩ p x

private theorem shifted_line_split (v u x : ℝ) :
    lineWeight v u x = Real.exp (-(2 * v * u)) * Real.exp (2 * v * x) := by
  rw [lineWeight, ← Real.exp_add]
  congr 1
  ring

private theorem line_integrable {I : Set ℝ} (v : I) (u : ℝ) (p : PositiveRealExponentialDecay I) :
    Integrable (fun x ↦ lineWeight v.val u x * ‖p.val x‖ ^ 2) := by
  have h := ((logExponentialDecayTwist I v p).memLp 2 volume).integrable_norm_pow (by norm_num : 2 ≠ 0)
  apply (h.const_mul (Real.exp (-(2 * v.val * u)))).congr
  filter_upwards with x
  rw [shifted_line_split, norm_twist_sq]
  ring

private theorem window_integrable {I : Set ℝ} (h0 : 0 ∈ I) {β : ℝ} (hβ : 0 ≤ β)
    (hβI : β ∈ I) (u : ℝ) (p : PositiveRealExponentialDecay I) :
    Integrable (fun x ↦ window β u x * ‖p.val x‖ ^ 2) := by
  refine (line_integrable ⟨β, hβI⟩ u p).mono' ?_ (Eventually.of_forall fun x ↦ ?_)
  · exact ((show Continuous (window β u) from by unfold window; fun_prop).mul
      ((profile_continuous h0 p).norm.pow 2)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (show 0 ≤ window β u x from (Real.exp_pos _).le) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (window_le_line β u x hβ).1 (sq_nonneg _)

private theorem line_energy_split {I : Set ℝ} (v u : ℝ) (p : PositiveRealExponentialDecay I) :
    energy (lineWeight v u) p = Real.exp (-(2 * v * u)) * ∫ x, Real.exp (2 * v * x) * ‖p.val x‖ ^ 2 := by
  simp only [energy, shifted_line_split, mul_assoc, integral_const_mul]

/-- Uniform bounds on two exponential lines imply a uniform bound in every
translate of the decaying two-sided exponential window. -/
private theorem window_energy_bound {I : Set ℝ} (h0 : 0 ∈ I) {β : ℝ} (hβ : 0 ≤ β)
    (hp : β ∈ I) (hm : -β ∈ I)
    (T : PositiveRealExponentialDecay I →ₗ[ℂ] PositiveRealExponentialDecay I)
    (hT : ∀ (v : I) (p : PositiveRealExponentialDecay I),
      ∫ x, Real.exp (2 * v.val * x) * ‖(T p).val x‖ ^ 2 ≤
        ∫ x, Real.exp (2 * v.val * x) * ‖p.val x‖ ^ 2)
    (u : ℝ) (p : PositiveRealExponentialDecay I) :
    energy (window β u) (T p) ≤ 2 * (1 + Real.exp (4 * β)) * energy (window β u) p := by
  let h (x : ℝ) : ℂ := Real.smoothTransition (x - u)
  have hh : h.HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal.comp <|
    smoothTransition_temperate.comp <| Function.HasTemperateGrowth.id'.sub (Function.HasTemperateGrowth.const u)
  let r := multiplyProfile h hh p
  let l := p - r
  have hlr (x : ℝ) : (T p).val x = (T l).val x + (T r).val x := by
    have he : T p = T l + T r := by rw [← map_add, sub_add_cancel]
    exact congrArg (fun q : PositiveRealExponentialDecay I ↦ q.val x) he
  have hleft (x : ℝ) : l.val x = ((1 - Real.smoothTransition (x - u) : ℝ) : ℂ) * p.val x := by
    change p.val x - h x * p.val x = _
    dsimp only [h]
    push_cast
    ring
  have hright (x : ℝ) : r.val x = (Real.smoothTransition (x - u) : ℂ) * p.val x := rfl
  have trans (v : I) (f : PositiveRealExponentialDecay I) :
      energy (lineWeight v.val u) (T f) ≤ energy (lineWeight v.val u) f := by
    rw [line_energy_split, line_energy_split]
    exact mul_le_mul_of_nonneg_left (hT v f) (Real.exp_pos _).le
  have hupp :
      energy (window β u) (T p) ≤ 2 * (energy (lineWeight β u) (T l) + energy (lineWeight (-β) u) (T r)) := by
    unfold energy
    rw [← integral_add (line_integrable ⟨β, hp⟩ u (T l)) (line_integrable ⟨-β, hm⟩ u (T r)),
      ← integral_const_mul]
    apply integral_mono (window_integrable h0 hβ hp u (T p)) (((line_integrable ⟨β, hp⟩ u (T l)).add
      (line_integrable ⟨-β, hm⟩ u (T r))).const_mul 2)
    intro x
    change window β u x * ‖(T p).val x‖ ^ 2 ≤
      2 * (lineWeight β u x * ‖(T l).val x‖ ^ 2 + lineWeight (-β) u x * ‖(T r).val x‖ ^ 2)
    rw [hlr x]
    have hs : ‖(T l).val x + (T r).val x‖ ^ 2 ≤ 2 * (‖(T l).val x‖ ^ 2 + ‖(T r).val x‖ ^ 2) := by
      exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans
        (by nlinarith [sq_nonneg (‖(T l).val x‖ - ‖(T r).val x‖)])
    have hpm := window_le_line β u x hβ
    have hmn : window β u x ≤ lineWeight (-β) u x := by simpa [lineWeight, mul_neg] using hpm.2
    calc
      _ ≤ window β u x * (2 * (‖(T l).val x‖ ^ 2 + ‖(T r).val x‖ ^ 2)) := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ = 2 * (window β u x * ‖(T l).val x‖ ^ 2 + window β u x * ‖(T r).val x‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hpm.1 (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hmn (sq_nonneg _))) (by norm_num)
  have hu (x : ℝ) : window β 0 (x - u) = window β u x := by simp [window]
  have hle : energy (lineWeight β u) l ≤ Real.exp (4 * β) * energy (window β u) p := by
    unfold energy
    rw [← integral_const_mul]
    apply integral_mono (line_integrable ⟨β, hp⟩ u l) ((window_integrable h0 hβ hp u p).const_mul _)
    intro x
    change lineWeight β u x * ‖l.val x‖ ^ 2 ≤ Real.exp (4 * β) * (window β u x * ‖p.val x‖ ^ 2)
    rw [hleft x, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one _)),
      mul_pow, ← mul_assoc, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((line_step_bounds β (x - u) hβ).2.trans_eq (by rw [hu])) (sq_nonneg _)
  have hre : energy (lineWeight (-β) u) r ≤ energy (window β u) p := by
    apply integral_mono (line_integrable ⟨-β, hm⟩ u r) (window_integrable h0 hβ hp u p)
    intro x
    change lineWeight (-β) u x * ‖r.val x‖ ^ 2 ≤ window β u x * ‖p.val x‖ ^ 2
    rw [hright x, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _),
      mul_pow, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa [lineWeight, mul_neg, hu] using (line_step_bounds β (x - u) hβ).1
  calc
    _ ≤ _ := hupp
    _ ≤ 2 * (energy (lineWeight β u) l + energy (lineWeight (-β) u) r) :=
      mul_le_mul_of_nonneg_left (add_le_add (trans ⟨β, hp⟩ l) (trans ⟨-β, hm⟩ r)) (by norm_num)
    _ ≤ 2 * (Real.exp (4 * β) * energy (window β u) p + energy (window β u) p) :=
      mul_le_mul_of_nonneg_left (add_le_add hle hre) (by norm_num)
    _ = _ := by ring

/-- The positive and negative halves of a decaying two-sided exponential have
equal finite mass. -/
private theorem laplace_mass {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (-c * |u - x|)) = ENNReal.ofReal (2 / c) := by
  let f (t : ℝ) := Real.exp (-c * |t|)
  have hlo : IntegrableOn f (Iic 0) := by
    apply (integrableOn_exp_mul_Iic hc 0).congr_fun _ measurableSet_Iic
    intro t ht
    simp [f, abs_of_nonpos (Set.mem_Iic.mp ht)]
  have hhi : IntegrableOn f (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0).congr_fun _ measurableSet_Ioi
    intro t ht
    simp [f, abs_of_nonneg (Set.mem_Ioi.mp ht).le]
  have hf : Integrable f := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    exact ⟨hlo, hhi⟩
  have h1 : ∫ t in Iic 0, f t = 1 / c := by
    calc
      _ = ∫ t : ℝ in Iic 0, Real.exp (c * t) :=
        setIntegral_congr_fun measurableSet_Iic (fun t ht ↦ by simp [f, abs_of_nonpos (Set.mem_Iic.mp ht)])
      _ = _ := by simp [integral_exp_mul_Iic hc]
  have h2 : ∫ t in Ioi 0, f t = 1 / c := by
    calc
      _ = ∫ t : ℝ in Ioi 0, Real.exp ((-c) * t) :=
        setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ by simp [f, abs_of_nonneg (Set.mem_Ioi.mp ht).le])
      _ = _ := by rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hc)]; simp
  rw [← ofReal_integral_eq_lintegral_ofReal (hf.comp_sub_right x) (Eventually.of_forall fun t ↦ (Real.exp_pos _).le)]
  change ENNReal.ofReal (∫ u : ℝ, f (u - x)) = _
  rw [integral_sub_right_eq_self f x, ← integral_add_compl (s := Iic (0:ℝ)) measurableSet_Iic hf,
    compl_Iic, h1, h2]
  congr 1
  ring

/-- If a density has a fixed exponential translation bound, convolution with
a faster two-sided exponential gives a uniformly comparable density. -/
private theorem compare_window_density {w : ℝ → ℝ} {κ β : ℝ} (hκ : 0 ≤ κ)
    (hm : ∀ u x, w u ≤ Real.exp (κ * |u - x|) * w x) (hβ : κ < 2 * β) (x : ℝ) :
    let mass := ∫⁻ u : ℝ, ENNReal.ofReal (window β u x * w u)
    ENNReal.ofReal (2 / (2 * β + κ)) * ENNReal.ofReal (w x) ≤ mass ∧
      mass ≤ ENNReal.ofReal (2 / (2 * β - κ)) * ENNReal.ofReal (w x) := by
  intro mass
  have shape (c : ℝ) (hc : 0 < c) :
      ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (-c * |u - x|) * w x) =
        ENNReal.ofReal (2 / c) * ENNReal.ofReal (w x) := by
    simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, laplace_mass hc]
  constructor
  · rw [← shape _ (by linarith)]
    apply lintegral_mono
    intro u
    apply ENNReal.ofReal_le_ofReal
    have hu : Real.exp (-κ * |u - x|) * w x ≤ w u := by
      have hh := mul_le_mul_of_nonneg_left (hm x u) (Real.exp_pos (-κ * |u - x|)).le
      rw [abs_sub_comm x u, ← mul_assoc, ← Real.exp_add, show -κ * |u - x| + κ * |u - x| = 0 by ring,
        Real.exp_zero, one_mul] at hh
      exact hh
    calc
      _ = Real.exp (-(2 * β) * |u - x|) * (Real.exp (-κ * |u - x|) * w x) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ window β u x * w u := by
        rw [window, abs_sub_comm x u]
        exact mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le
  · rw [← shape _ (sub_pos.mpr hβ)]
    apply lintegral_mono
    intro u
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ window β u x * (Real.exp (κ * |u - x|) * w x) := mul_le_mul_of_nonneg_left (hm u x) (Real.exp_pos _).le
      _ = _ := by
        rw [window, abs_sub_comm x u, ← mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- A weighted square norm written with a nonnegative integral. -/
private def eEnergy {I : Set ℝ} (w : ℝ → ℝ) (p : PositiveRealExponentialDecay I) :=
  ∫⁻ (x : ℝ), ENNReal.ofReal (w x) * ENNReal.ofReal (‖p.val x‖ ^ 2)

private theorem eEnergy_eq {I : Set ℝ} {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x) (p : PositiveRealExponentialDecay I)
    (hi : Integrable (fun x ↦ w x * ‖p.val x‖ ^ 2)) :
    eEnergy w p = ENNReal.ofReal (energy w p) := by
  unfold eEnergy energy
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x ↦ mul_nonneg (hw x) (sq_nonneg _))]
  simp_rw [ENNReal.ofReal_mul (hw _)]

/-- The contractions on both vertical lines give a bound for the squared norm, uniform in
the multiplier, for any continuous density with controlled translation growth. -/
private theorem eEnergy_bound {I : Set ℝ} (h0 : 0 ∈ I) {β κ : ℝ} (hκ : 0 ≤ κ) (hβ : κ < 2 * β)
    (hp : β ∈ I) (hm : -β ∈ I) (w : ℝ → ℝ) (hwc : Continuous w)
    (hmod : ∀ u x, w u ≤ Real.exp (κ * |u - x|) * w x)
    (T : PositiveRealExponentialDecay I →ₗ[ℂ] PositiveRealExponentialDecay I)
    (hT : ∀ (v : I) (p : PositiveRealExponentialDecay I),
      ∫ x, Real.exp (2 * v.val * x) * ‖(T p).val x‖ ^ 2 ≤
        ∫ x, Real.exp (2 * v.val * x) * ‖p.val x‖ ^ 2)
    (p : PositiveRealExponentialDecay I) :
    ENNReal.ofReal (2 / (2 * β + κ)) * eEnergy w (T p) ≤
      (ENNReal.ofReal (2 * (1 + Real.exp (4 * β))) * ENNReal.ofReal (2 / (2 * β - κ))) * eEnergy w p := by
  let K (u x : ℝ) := ENNReal.ofReal (window β u x * w u)
  let R (p : PositiveRealExponentialDecay I) (x : ℝ) := ENNReal.ofReal (‖p.val x‖ ^ 2)
  let C := ENNReal.ofReal (2 * (1 + Real.exp (4 * β)))
  have hR (p : PositiveRealExponentialDecay I) : Measurable (R p) :=
    ((profile_continuous h0 p).norm.pow 2).measurable.ennreal_ofReal
  have hK : Measurable (uncurry K) := by
    change Measurable (fun t : ℝ × ℝ ↦ ENNReal.ofReal (Real.exp (-(2 * β) * |t.2 - t.1|) * w t.1))
    fun_prop
  have pull (u : ℝ) (f : PositiveRealExponentialDecay I) :
      ∫⁻ x, K u x * R f x = ENNReal.ofReal (w u) * ENNReal.ofReal (energy (window β u) f) := by
    have hw0 (x : ℝ) : 0 ≤ window β u x := (Real.exp_pos _).le
    simp only [K, ENNReal.ofReal_mul (hw0 _)]
    simp_rw [mul_comm (ENNReal.ofReal (window β u _)) (ENNReal.ofReal (w u)), mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact congrArg _ (eEnergy_eq (fun _ ↦ (Real.exp_pos _).le) f (window_integrable h0 (by linarith) hp u f))
  have hh (u : ℝ) : ∫⁻ x, K u x * R (T p) x ≤ C * ∫⁻ x, K u x * R p x := by
    rw [pull, pull, mul_left_comm]
    apply mul_le_mul' le_rfl
    change ENNReal.ofReal _ ≤ ENNReal.ofReal _ * ENNReal.ofReal _
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (1 + Real.exp (4 * β)))]
    exact ENNReal.ofReal_le_ofReal (window_energy_bound h0 (by linarith) hp hm T hT u p)
  have avg := integrate_window_bounds volume volume K hK (R p) (R (T p)) (hR _) (hR _) C hh
  have factor (d : ℝ) (f : PositiveRealExponentialDecay I) :
      ENNReal.ofReal d * eEnergy w f = ∫⁻ x, (ENNReal.ofReal d * ENNReal.ofReal (w x)) * R f x := by
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  calc
    _ = _ := factor _ (T p)
    _ ≤ ∫⁻ x, (∫⁻ u, K u x) * R (T p) x := lintegral_mono fun x ↦ mul_le_mul'
      (compare_window_density hκ hmod hβ x).1 le_rfl
    _ ≤ _ := avg
    _ ≤ C * (ENNReal.ofReal (2 / (2 * β - κ)) * eEnergy w p) := by
      rw [factor]
      exact mul_le_mul' le_rfl (lintegral_mono fun x ↦ mul_le_mul' (compare_window_density hκ hmod hβ x).2 le_rfl)
    _ = _ := (mul_assoc _ _ _).symm

private theorem polynomial_shift (x d : ℝ) :
    1 + (x + d) ^ 2 ≤ (1 + |d|) ^ 2 * (1 + x ^ 2) := by
  rcases le_total 0 d with h | h
  · rw [abs_of_nonneg h]
    nlinarith [mul_nonneg h (sq_nonneg (x - 1)), mul_nonneg h (sq_nonneg x), sq_nonneg (d * x)]
  · rw [abs_of_nonpos h]
    nlinarith [mul_nonneg (neg_nonneg.mpr h) (sq_nonneg (x + 1)),
      mul_nonneg (neg_nonneg.mpr h) (sq_nonneg x), sq_nonneg (d * x)]

/-- An explicit exponential translation bound for the actual symmetric
Hardy–Sobolev weight. -/
private theorem density_translation {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (u x : ℝ) :
    intervalSobolevDensity (-α) α s u ≤ Real.exp ((2 * α + s) * |u - x|) * intervalSobolevDensity (-α) α s x := by
  let d := u - x
  have hd : x + d = u := by dsimp [d]; ring
  have hsum : |u| ≤ |d| + |x| := by simpa only [← hd, add_comm |d|] using abs_add_le x d
  have hpoly : 1 + u ^ 2 ≤ Real.exp (2 * |d|) * (1 + x ^ 2) := by
    calc
      _ ≤ (1 + |d|) ^ 2 * (1 + x ^ 2) := hd ▸ polynomial_shift x d
      _ ≤ (Real.exp |d|) ^ 2 * (1 + x ^ 2) := by
        gcongr
        linarith [Real.add_one_le_exp |d|]
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hp : (1 + u ^ 2) ^ (s / 2) ≤ Real.exp (s * |d|) * (1 + x ^ 2) ^ (s / 2) := by
    calc
      _ ≤ (Real.exp (2 * |d|) * (1 + x ^ 2)) ^ (s / 2) := Real.rpow_le_rpow (by positivity) hpoly (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (Real.exp_pos _).le (by positivity), ← Real.exp_mul]
        congr 2
        ring
  have hx : Real.exp (2 * α * |u|) ≤ Real.exp (2 * α * |d|) * Real.exp (2 * α * |x|) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ 2 * α)]
  rw [symmIntervalSobolevDensity_eq hα, symmIntervalSobolevDensity_eq hα]
  calc
    _ ≤ (Real.exp (2 * α * |d|) * Real.exp (2 * α * |x|)) * (Real.exp (s * |d|) * (1 + x ^ 2) ^ (s / 2)) :=
      mul_le_mul hx hp (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = _ := by
      rw [show (2 * α + s) * |u - x| = 2 * α * |d| + s * |d| by dsimp [d]; ring, Real.exp_add]
      ring

private theorem eEnergy_rep {I : Set ℝ} {w : ℝ → ℝ} (hw : Measurable w)
    (p : PositiveRealExponentialDecay I)
    (e : Lp ℂ 2 (volume.withDensity fun x ↦ ENNReal.ofReal (w x)))
    (he : (e : ℝ → ℂ) =ᵐ[volume] p.val) :
    eEnergy w p = ENNReal.ofReal (‖e‖ ^ 2) := by
  let ν := volume.withDensity fun x ↦ ENNReal.ofReal (w x)
  have h := (Lp.memLp e).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hi := ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall fun x ↦ sq_nonneg ‖e x‖)
  rw [L2.integral_sq_norm (𝕜 := ℂ)] at hi
  rw [hi, lintegral_withDensity_eq_lintegral_mul_non_measurable volume hw.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply lintegral_congr_ae
  filter_upwards [he] with x hx
  change _ = ENNReal.ofReal (w x) * ENNReal.ofReal (‖e x‖ ^ 2)
  rw [hx]

/-- Every contraction on the vertical test lines extends to the symmetric
Hardy–Sobolev space with a bound depending only on the widths and degree. -/
private theorem scalar_sobolev_multiplier_extension {I : Set ℝ} (h0 : 0 ∈ I)
    {α s β : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hβ : 2 * α + s < 2 * β)
    (hp : β ∈ I) (hm : -β ∈ I)
    (j : PositiveRealExponentialDecay I →L[ℂ] CompactIntervalSobolev volume id (-α) α s)
    (hd : DenseRange j) (hr : ∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : PositiveRealExponentialDecay I →ₗ[ℂ] PositiveRealExponentialDecay I),
      (∀ (v : I) (p : PositiveRealExponentialDecay I),
        ∫ x, Real.exp (2 * v.val * x) * ‖(T p).val x‖ ^ 2 ≤ ∫ x, Real.exp (2 * v.val * x) * ‖p.val x‖ ^ 2) →
      ∃ U : CompactIntervalSobolev volume id (-α) α s →L[ℂ] CompactIntervalSobolev volume id (-α) α s,
        ‖U‖ ≤ C ∧ ∀ p, U (j p) = j (T p) := by
  let w := intervalSobolevDensity (-α) α s
  let κ := 2 * α + s
  let A := 2 / (2 * β + κ)
  let D := 2 / (2 * β - κ)
  let B := 2 * (1 + Real.exp (4 * β))
  have hk : 0 ≤ κ := by dsimp [κ]; positivity
  have hab : κ < 2 * β := hβ
  have hA : 0 < A := div_pos (by norm_num) (by linarith)
  have hD : 0 < D := div_pos (by norm_num) (sub_pos.mpr hab)
  have hB : 0 < B := by dsimp [B]; positivity
  have hc : Continuous w := by
    have hfun : w = fun x ↦ Real.exp (2 * α * |x|) * (1 + x ^ 2) ^ (s / 2) := funext (symmIntervalSobolevDensity_eq hα s)
    rw [hfun]
    exact Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) (fun x ↦ Or.inl (by positivity)))
  let C := Real.sqrt ((B * D) / A)
  refine ⟨C, Real.sqrt_nonneg _, fun T ht ↦ ?_⟩
  have hbound (p : PositiveRealExponentialDecay I) : ‖j (T p)‖ ≤ C * ‖j p‖ := by
    have H := eEnergy_bound h0 hk hab hp hm w hc (density_translation hα hs) T ht p
    have rep (q : PositiveRealExponentialDecay I) :
        eEnergy w q = ENNReal.ofReal (‖j q‖ ^ 2) := eEnergy_rep hc.measurable q (j q) (hr q)
    change ENNReal.ofReal A * eEnergy w (T p) ≤ ENNReal.ofReal B * ENNReal.ofReal D * eEnergy w p at H
    rw [rep, rep, ← ENNReal.ofReal_mul hA.le, ← ENNReal.ofReal_mul hB.le,
      ← ENNReal.ofReal_mul (mul_nonneg hB.le hD.le)] at H
    have h := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ B * D * ‖j p‖ ^ 2)).mp H
    have hsq : ‖j (T p)‖ ^ 2 ≤ ((B * D) / A) * ‖j p‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hA]
      linarith only [h, mul_comm A (‖j (T p)‖ ^ 2)]
    calc
      _ = Real.sqrt (‖j (T p)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (((B * D) / A) * ‖j p‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _) ]
  let t := j.toLinearMap.comp T
  let U := t.extendOfNorm j.toLinearMap
  exact ⟨U, U.opNorm_le_bound (Real.sqrt_nonneg _) (LinearMap.norm_extendOfNorm_apply_le hd C hbound),
    LinearMap.extendOfNorm_eq hd ⟨C, hbound⟩⟩

/-- Pull pointwise multiplication by a contractive holomorphic symbol on a strip back to
its exponential test profiles by the Fourier–Mellin equivalence. -/
private def multiplyTest {I : Set ℝ} (hI : IsOpen I) (hi : OrdConnected I) (hne : I.Nonempty)
    (b : ℂ → ℂ) (hb : DifferentiableOn ℂ b (Complex.re ⁻¹' I)) (hc : ∀ z, z.re ∈ I → ‖b z‖ ≤ 1) :
    PositiveRealExponentialDecay I →ₗ[ℂ] PositiveRealExponentialDecay I :=
  let M := positiveRealFourierMellin I hI hi hne
  let B : SchwartzBergman I →ₗ[ℂ] SchwartzBergman I :=
    { toFun := fun H ↦ ⟨_, multiply_mem H b hb hc⟩
      map_add' := fun H K ↦ Subtype.ext (funext fun z ↦ mul_add (b z) (H.val z) (K.val z))
      map_smul' := fun c H ↦ Subtype.ext (funext fun z ↦ mul_left_comm (b z) c (H.val z)) }
  M.symm.toLinearMap.comp (B.comp M.toLinearMap)

/-- The Mellin transform of a multiplied test is the product of its transform with the symbol. -/
private theorem multiplyTest_mellin {I : Set ℝ} (hI : IsOpen I) (hi : OrdConnected I) (hne : I.Nonempty)
    (b : ℂ → ℂ) (hb : DifferentiableOn ℂ b (Complex.re ⁻¹' I)) (hc : ∀ z, z.re ∈ I → ‖b z‖ ≤ 1)
    (p : PositiveRealExponentialDecay I) (z : ℂ) (hz : z.re ∈ I) :
    mellin (fun t ↦ (multiplyTest hI hi hne b hb hc p).val (Real.log t)) z =
      b z * mellin (fun t ↦ p.val (Real.log t)) z := by
  let M := positiveRealFourierMellin I hI hi hne
  let G : SchwartzBergman I := ⟨_, multiply_mem (M p) b hb hc⟩
  change mellin (fun t ↦ (M.symm G).val (Real.log t)) z = _
  rw [← positiveRealFourierMellin_apply I hI hi hne (M.symm G) z hz]
  change (M (M.symm G)).val z = _
  rw [M.apply_symm_apply]
  exact congrArg (b z * ·) (positiveRealFourierMellin_apply I hI hi hne p z hz)

/-- The multiplier on exponential tests is a contraction for the unweighted vertical
Plancherel norms on each Mellin line. In logarithmic coordinates the squared norm has
density `exp (2 * v * x)`. -/
private theorem multiplyTest_line_contraction {I : Set ℝ} (hI : IsOpen I) (hi : OrdConnected I)
    (hne : I.Nonempty) (b : ℂ → ℂ) (hb : DifferentiableOn ℂ b (Complex.re ⁻¹' I))
    (hc : ∀ z, z.re ∈ I → ‖b z‖ ≤ 1) (v : I) (p : PositiveRealExponentialDecay I) :
    ∫ x, Real.exp (2 * v.val * x) * ‖(multiplyTest hI hi hne b hb hc p).val x‖ ^ 2 ≤
      ∫ x, Real.exp (2 * v.val * x) * ‖p.val x‖ ^ 2 := by
  apply line_contraction
  intro t
  rw [multiplyTest_mellin hI hi hne b hb hc p ⟨v, t⟩ v.property, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hc _ v.property)

/-- If the symbols are contractive on the open strip and converge to one pointwise,
their inverse Fourier–Mellin multipliers converge to the identity in the test topology. -/
private theorem tendsto_multiplyTest {I : Set ℝ} (hI : IsOpen I) (hi : OrdConnected I) (hne : I.Nonempty)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] (p : PositiveRealExponentialDecay I)
    (b : ι → ℂ → ℂ) (hb : ∀ n, DifferentiableOn ℂ (b n) (Complex.re ⁻¹' I))
    (hc : ∀ n z, z.re ∈ I → ‖b n z‖ ≤ 1)
    (hl : ∀ z, z.re ∈ I → Tendsto (fun n ↦ b n z) l (𝓝 1)) :
    Tendsto (fun n ↦ multiplyTest hI hi hne (b n) (hb n) (hc n) p) l (𝓝 p) := by
  let M := positiveRealFourierMellin I hI hi hne
  let G n : SchwartzBergman I := ⟨_, multiply_mem (M p) (b n) (hb n) (hc n)⟩
  have hg : Tendsto G l (𝓝 (M p)) := tendsto_multiply (M p) b hb hc hl
  have hq := (M.symm.continuous.tendsto (M p)).comp hg
  rw [M.symm_apply_apply] at hq
  exact hq

/-- Contractive holomorphic multipliers on a wider vertical strip act uniformly
boundedly on the full Hardy–Sobolev norm. Pointwise convergence to one implies
strong convergence on that whole space. -/
private theorem exists_sobolev_mellin_multiplier_family {I : Set ℝ} (hI : IsOpen I) (hi : OrdConnected I)
    (h0 : 0 ∈ I) {α s β : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hβ : 2 * α + s < 2 * β)
    (hp : β ∈ I) (hm : -β ∈ I) (hsub : Icc (-α) α ⊆ I)
    {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated] (b : ι → ℂ → ℂ)
    (hb : ∀ n, DifferentiableOn ℂ (b n) (Complex.re ⁻¹' I)) (hc : ∀ n z, z.re ∈ I → ‖b n z‖ ≤ 1)
    (hl : ∀ z, z.re ∈ I → Tendsto (fun n ↦ b n z) l (𝓝 1)) :
    let E := CompactIntervalSobolev volume id (-α) α s
    ∃ (j : PositiveRealExponentialDecay I →L[ℂ] E) (U : ι → E →L[ℂ] E) (C : ℝ),
      Injective j ∧ DenseRange j ∧ (∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val) ∧
      (∀ n, ‖U n‖ ≤ C) ∧ (∀ y, Tendsto (fun n ↦ U n y) l (𝓝 y)) ∧
      ∀ p n, ∃ q : PositiveRealExponentialDecay I, U n (j p) = j q ∧
        ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
          b n z * mellin (fun t ↦ p.val (Real.log t)) z := by
  intro E
  have hne : I.Nonempty := ⟨0, h0⟩
  obtain ⟨j, hinj, hd, hr⟩ := scalarIntervalSobolev_dense (-α) α s (by linarith) hs I hI hi hsub
  obtain ⟨C, hC, H⟩ := scalar_sobolev_multiplier_extension h0 hα hs hβ hp hm j hd hr
  let T n := multiplyTest hI hi hne (b n) (hb n) (hc n)
  choose U hu he using fun n ↦ H (T n)
    (multiplyTest_line_contraction hI hi hne (b n) (hb n) (hc n))
  refine ⟨j, U, C, hinj, hd, hr, hu, ?_, fun p n ↦
    ⟨T n p, he n p, multiplyTest_mellin hI hi hne (b n) (hb n) (hc n) p⟩⟩
  have hnorm : ∃ M ≥ 0, ∀ n, ‖U n‖ ≤ M := ⟨C, hC, hu⟩
  have hequi : Equicontinuous (fun n ↦ ⇑(U n)) :=
    ((NormedSpace.equicontinuous_tfae U).out 2 7).mpr hnorm
  intro y
  apply (hequi y).tendsto_of_mem_closure (s := Set.range j) (f := id)
    continuousWithinAt_id _ (hd y)
  rintro _ ⟨p, rfl⟩
  simp_rw [he]
  apply (j.continuous.tendsto p).comp
  exact tendsto_multiplyTest hI hi hne p b hb hc hl

end StripMultiplier

end

section

open Filter Function MeasureTheory Set
open scoped Topology

namespace StripDual

local notation "Tests" => (schwartzBergmanSubmodule (Set.univ : Set ℝ))

local notation "SE" => (fun α s : ℝ ↦ CompactIntervalSobolev volume id (-α) α s)

/-- The Fourier–Mellin equivalence on the whole plane. The inverse sends an entire test
to its radial profile in logarithmic coordinates. -/
private def ME := positiveRealFourierMellin (univ : Set ℝ) isOpen_univ ordConnected_univ univ_nonempty

/-- Pointwise multiplication of entire Schwartz–Bergman tests, linear in the second factor. -/
private def timesTest (H : Tests) : Tests →ₗ[ℂ] Tests where
  toFun K := ⟨fun z ↦ H.val z * K.val z, by
    refine ⟨by simp, H.property.2.1.mul K.property.2.1, ?_⟩
    intro a b hab hsub n
    obtain ⟨C, hC⟩ := H.property.2.2 a b hab hsub n
    obtain ⟨D, hD⟩ := K.property.2.2 a b hab hsub 0
    refine ⟨max C 0 * max D 0, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖z ^ n * (H.val z * K.val z)‖ ≤ _
    rw [← mul_assoc, norm_mul]
    apply mul_le_mul ((hC ⟨z, hz, rfl⟩).trans (le_max_left _ _)) _ (norm_nonneg _) (le_max_right _ _)
    simpa using (hD ⟨z, hz, rfl⟩).trans (le_max_left D 0)⟩
  map_add' K L := Subtype.ext (funext fun z ↦ mul_add (H.val z) (K.val z) (L.val z))
  map_smul' c K := Subtype.ext (funext fun z ↦ mul_left_comm (H.val z) c (K.val z))

private def restrictProfile (J : Set ℝ) (p : PositiveRealExponentialDecay univ) : PositiveRealExponentialDecay J :=
  ⟨p.val, (Submodule.mem_iInf _).mpr fun a ↦ (Submodule.mem_iInf _).mp p.property ⟨a.val, mem_univ _⟩⟩

private theorem inverseSymbol (H : Tests) (z : ℂ) :
    mellin (fun t ↦ (ME.symm H).val (Real.log t)) z = H.val z := by
  rw [← positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty (ME.symm H) z (mem_univ _)]
  exact congrArg (fun K : SchwartzBergman univ ↦ K.val z) (ME.apply_symm_apply H)

private theorem eqProfile {I : Set ℝ} (hI : IsOpen I) (hi : OrdConnected I) (hne : I.Nonempty)
    (p q : PositiveRealExponentialDecay I)
    (h : ∀ z, z.re ∈ I → mellin (fun t ↦ p.val (Real.log t)) z = mellin (fun t ↦ q.val (Real.log t)) z) :
    p = q := by
  let M := positiveRealFourierMellin I hI hi hne
  apply M.injective
  apply Subtype.ext
  funext z
  by_cases hz : z.re ∈ I
  · exact (positiveRealFourierMellin_apply I hI hi hne p z hz).trans ((h z hz).trans
      (positiveRealFourierMellin_apply I hI hi hne q z hz).symm)
  · exact ((M p).property.1 hz).trans ((M q).property.1 hz).symm

/-- Entire Schwartz–Bergman tests map densely into the scalar Sobolev space.
Their representatives are the logarithmic inverse Fourier–Mellin transforms. -/
private theorem exists_chart {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ∃ e : Tests →ₗ[ℂ] SE α s, DenseRange e ∧
      ∀ H, (e H : ℝ → ℂ) =ᵐ[volume] (ME.symm H).val := by
  obtain ⟨j, -, hd, hr⟩ :=
    scalarIntervalSobolev_dense (-α) α s (by linarith) hs univ isOpen_univ ordConnected_univ (subset_univ _)
  let e : Tests →ₗ[ℂ] SE α s := j.toLinearMap.comp ME.symm.toLinearMap
  exact ⟨e, hd.comp ME.symm.surjective.denseRange j.continuous, fun H ↦ hr _⟩

private theorem chart_restriction {α s : ℝ} (J : Set ℝ) (e : Tests →ₗ[ℂ] SE α s)
    (he : ∀ H, (e H : ℝ → ℂ) =ᵐ[volume] (ME.symm H).val)
    (j : PositiveRealExponentialDecay J →L[ℂ] SE α s) (hj : ∀ q, (j q : ℝ → ℂ) =ᵐ[volume] q.val) (H : Tests) :
    e H = j (restrictProfile J (ME.symm H)) := by
  apply Lp.ext
  exact (withDensity_absolutelyContinuous _ _).ae_le ((he H).trans (hj (restrictProfile J (ME.symm H))).symm)

/-- In any chart with the correct radial representatives, multiplication by an entire
Schwartz–Bergman test extends to a continuous operator on the Sobolev space. -/
private theorem chart_multiplier_action {α s β r : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hβ : 2 * α + s < 2 * β) (hβr : β < r)
    (e : Tests →ₗ[ℂ] SE α s) (he : ∀ H, (e H : ℝ → ℂ) =ᵐ[volume] (ME.symm H).val) :
    ∀ H : Tests, ∃ U : SE α s →L[ℂ] SE α s, ∀ p, U (e p) = e (timesTest H p) := by
  let J := Ioo (-r) r
  have hr : 0 < r := by linarith
  have h0 : 0 ∈ J := ⟨by linarith, hr⟩
  have hp : β ∈ J := ⟨by linarith, hβr⟩
  have hm : -β ∈ J := ⟨by linarith, by linarith⟩
  have hsub : Icc (-α) α ⊆ J := fun x ⟨hl, hu⟩ ↦ ⟨by linarith, by linarith⟩
  obtain ⟨j, -, hd, hj⟩ :=
    scalarIntervalSobolev_dense (-α) α s (by linarith) hs J isOpen_Ioo ordConnected_Ioo hsub
  obtain ⟨C, hC, extend⟩ := StripMultiplier.scalar_sobolev_multiplier_extension h0 hα hs hβ hp hm j hd hj
  have contract (H : Tests) (hbounded : ∀ z, z.re ∈ J → ‖H.val z‖ ≤ 1) :
      ∃ U : SE α s →L[ℂ] SE α s, ∀ p, U (e p) = e (timesTest H p) := by
    have hdiff : DifferentiableOn ℂ H.val (Complex.re ⁻¹' J) := H.property.2.1.mono (fun _ _ ↦ trivial)
    let T := StripMultiplier.multiplyTest isOpen_Ioo ordConnected_Ioo ⟨0, h0⟩ H.val hdiff hbounded
    obtain ⟨U, -, hU⟩ := extend T (StripMultiplier.multiplyTest_line_contraction
      isOpen_Ioo ordConnected_Ioo ⟨0, h0⟩ H.val hdiff hbounded)
    refine ⟨U, fun p ↦ ?_⟩
    rw [chart_restriction J e he j hj p, hU, chart_restriction J e he j hj (timesTest H p)]
    apply congrArg j
    apply eqProfile isOpen_Ioo ordConnected_Ioo ⟨0, h0⟩
    intro z hz
    rw [StripMultiplier.multiplyTest_mellin isOpen_Ioo ordConnected_Ioo ⟨0, h0⟩ H.val hdiff hbounded _ z hz]
    change H.val z * mellin (fun t ↦ (ME.symm p).val (Real.log t)) z =
      mellin (fun t ↦ (ME.symm (timesTest H p)).val (Real.log t)) z
    rw [inverseSymbol, inverseSymbol]
    rfl
  intro H
  obtain ⟨M, hM⟩ := H.property.2.2 (-r) r (by linarith) (subset_univ _) 0
  let A := max M 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let h : Tests := (A : ℂ)⁻¹ • H
  have hb (z : ℂ) (hz : z.re ∈ J) : ‖h.val z‖ ≤ 1 := by
    change ‖(A : ℂ)⁻¹ * H.val z‖ ≤ 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA, inv_mul_eq_div]
    apply (div_le_one hA).mpr
    have hz' : z ∈ Complex.re ⁻¹' Icc (-r) r := ⟨hz.1.le, hz.2.le⟩
    exact (by simpa using hM ⟨z, hz', rfl⟩ : ‖H.val z‖ ≤ M).trans (le_max_left _ _)
  obtain ⟨U, hU⟩ := contract h hb
  refine ⟨(A : ℂ) • U, fun p ↦ ?_⟩
  rw [smul_apply, hU, ← e.map_smul]
  apply congrArg e
  apply Subtype.ext
  funext z
  change (A : ℂ) * (((A : ℂ)⁻¹ * H.val z) * p.val z) = H.val z * p.val z
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hA.ne'), one_mul]

/-- Contractive holomorphic cutoffs tending pointwise to one on a wider strip give
operators converging strongly to the identity. On each test vector their Mellin transforms
agree with pointwise multiplication by the cutoffs throughout the wider strip. -/
private theorem chart_tail_action {α s β r : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) (hβ : 2 * α + s < 2 * β) (hβr : β < r)
    (e : Tests →ₗ[ℂ] SE α s) (he : ∀ H, (e H : ℝ → ℂ) =ᵐ[volume] (ME.symm H).val)
    {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated] (b : ι → ℂ → ℂ)
    (hb : ∀ n, DifferentiableOn ℂ (b n) (Complex.re ⁻¹' Ioo (-r) r))
    (hc : ∀ n z, z.re ∈ Ioo (-r) r → ‖b n z‖ ≤ 1)
    (hl : ∀ z, z.re ∈ Ioo (-r) r → Tendsto (fun n ↦ b n z) l (𝓝 1)) :
    ∃ U : ι → SE α s →L[ℂ] SE α s, (∀ y, Tendsto (fun n ↦ U n y) l (𝓝 y)) ∧
      ∀ n H, ∃ q : PositiveRealExponentialDecay (Ioo (-r) r), (U n (e H) : ℝ → ℂ) =ᵐ[volume] q.val ∧
        ∀ z, z.re ∈ Ioo (-r) r → mellin (fun t ↦ q.val (Real.log t)) z = b n z * H.val z := by
  let J := Ioo (-r) r
  have h0 : 0 ∈ J := ⟨by linarith, by linarith⟩
  obtain ⟨j, U, -, -, -, hj, -, hlim, hU⟩ := StripMultiplier.exists_sobolev_mellin_multiplier_family
    isOpen_Ioo ordConnected_Ioo h0 ha hs hβ (⟨by linarith, hβr⟩ : β ∈ J) (⟨by linarith, by linarith⟩ : -β ∈ J)
    (fun x ⟨hx, hy⟩ ↦ ⟨by linarith, by linarith⟩) l b hb hc hl
  refine ⟨U, hlim, fun n H ↦ ?_⟩
  obtain ⟨q, hq, hm⟩ := hU (restrictProfile J (ME.symm H)) n
  refine ⟨q, ?_, fun z hz ↦ (hm z hz).trans (congrArg (b n z * ·) (inverseSymbol H z))⟩
  rw [chart_restriction J e he j hj, hq]
  exact hj q

end StripDual

end

/-! ### Recovering the weighted theta closure

In one compact character component, multiplication by the complementary Blaschke products
of a single polar-free generator converges strongly in the scalar strip space. Each product
reduces approximation to a finite set of Taylor functionals. The functions that annihilate
the whole theta ideal have precisely the Hecke vanishing orders. Haar averaging then
recovers approximation in the full strip space. This gives a separate proof of the
density assertions in Theorem 10.2.2.1, p. 446. -/

section StripThetaSynthesis

local notation "SE" => (fun α s : ℝ ↦ CompactIntervalSobolev volume id (-α) α s)
local notation "Tests" => ↥(schwartzBergmanSubmodule (Set.univ : Set ℝ))

namespace StripDual
open Filter Finset Set Function

section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A continuous linear combination of one finite Jordan chain can contain a highest
nonzero coefficient only if every jet up to and including that degree is continuous.
The lowering map models precomposition with a bounded smooth coordinate multiplier. -/
private theorem stripBounded_chain (B : Submodule ℂ V) (v : ℕ → V)
    (T : V →ₗ[ℂ] V) (hT : ∀ x ∈ B, T x ∈ B) (h0 : T (v 0) = 0)
    (n : ℕ) (hS : ∀ j, j < n → T (v (j + 1)) = ((j + 1 : ℕ) : ℂ) • v j)
    (c : ℕ → ℂ) (hL : (∑ k ∈ range (n+1), c k • v k) ∈ B) (hc : c n ≠ 0) :
    ∀ k ≤ n, v k ∈ B := by
  have hcancel {d : ℂ} {x : V} (hd : d ≠ 0) (h : d • x ∈ B) : x ∈ B := by
    simpa [smul_smul, hd] using B.smul_mem d⁻¹ h
  induction n generalizing c with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst k
    exact hcancel hc (by simpa using hL)
  | succ n ih =>
    have drop : T (∑ k ∈ range (n + 1 + 1), c k • v k) =
        ∑ j ∈ range (n+1), (c (j+1) * (j+1 : ℕ)) • v j := by
      rw [Finset.sum_range_succ', map_add, map_sum, map_smul, h0, smul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul, hS j (Finset.mem_range.mp hj), smul_smul]
    have hprev := ih (fun j hj ↦ hS j (by omega)) (fun j ↦ c (j+1) * (j+1 : ℕ))
      (drop ▸ hT _ hL) (mul_ne_zero hc (by exact_mod_cast Nat.succ_ne_zero n))
    intro k hk
    rcases Nat.lt_or_eq_of_le hk with hk | rfl
    · exact hprev k (by omega)
    · apply hcancel hc
      have hlo : (∑ j ∈ Finset.range (n + 1), c j • v j) ∈ B :=
        B.sum_mem fun j hj ↦ B.smul_mem (c j) (hprev j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      simpa only [Finset.sum_range_succ (f := fun j ↦ c j • v j) (n := n+1),
        add_sub_cancel_left] using B.sub_mem hL hlo

/-- Vanishing higher coefficients do not affect the separation of the supported terms. -/
private theorem stripBounded_terms (B : Submodule ℂ V) (v : ℕ → V)
    (T : V →ₗ[ℂ] V) (hT : ∀ x ∈ B, T x ∈ B) (h0 : T (v 0) = 0)
    (n : ℕ) (hS : ∀ j, j + 1 < n → T (v (j + 1)) = ((j + 1 : ℕ) : ℂ) • v j)
    (c : ℕ → ℂ) (hL : (∑ k ∈ range n, c k • v k) ∈ B) :
    ∀ k < n, c k ≠ 0 → v k ∈ B := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : c n = 0
    · have hprev := ih (fun j hj ↦ hS j (by omega)) (by simpa [Finset.sum_range_succ, hn] using hL)
      intro k hk hck
      have hkn : k ≠ n := fun e ↦ hck (e ▸ hn)
      exact hprev k (by omega) hck
    · exact fun k hk _ ↦ stripBounded_chain B v T hT h0 n (fun j hj ↦ hS j (by omega)) c hL hn k (by omega)

/-- A bounded finite jet combination at multiple points can only use bounded individual
jets. The cutoff multiplier selects a single frequency and its coordinate multiple
lowers the ordinary derivative jet exactly by its integer degree. -/
private theorem stripBounded_multijets {Z : Type*} [Fintype Z] [DecidableEq Z]
    (B : Submodule ℂ V) (v : Z → ℕ → V) (d : Z → ℕ)
    (P T : Z → V →ₗ[ℂ] V)
    (hP : ∀ z x, x ∈ B → P z x ∈ B) (hT : ∀ z x, x ∈ B → T z x ∈ B)
    (hcut : ∀ z w k, k < d w → P z (v w k) = if z = w then v w k else 0)
    (h0 : ∀ z, T z (v z 0) = 0)
    (hS : ∀ z k, k + 1 < d z → T z (v z (k + 1)) = ((k + 1 : ℕ) : ℂ) • v z k)
    (c : Z → ℕ → ℂ) (hL : (∑ z, ∑ k ∈ range (d z), c z k • v z k) ∈ B) :
    ∀ z k, k < d z → c z k ≠ 0 → v z k ∈ B := by
  intro z
  have hproj : P z (∑ w, ∑ k ∈ range (d w), c w k • v w k) =
      ∑ k ∈ range (d z), c z k • v z k := by
    simp only [map_sum, map_smul]
    rw [Finset.sum_eq_single z]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [hcut z z k (Finset.mem_range.mp hk), ite_eq_left rfl]
    · intro w _ hw
      apply Finset.sum_eq_zero
      intro k hk
      rw [hcut z w k (Finset.mem_range.mp hk), ite_eq_right (Ne.symm hw), smul_zero]
    · simp
  exact stripBounded_terms B (v z) (T z) (hT z) (h0 z) (d z) (hS z) (c z)
    (hproj ▸ hP z _ hL)
end

private theorem test_analytic (H : Tests) (w : ℂ) : AnalyticAt ℂ H.val w :=
  (differentiableOn_univ.mp (by simpa using H.property.2.1)).analyticAt w

private def jet (w : ℂ) (k : ℕ) : Module.Dual ℂ Tests where
  toFun H := iteratedDeriv k H.val w
  map_add' H K := iteratedDeriv_fun_add (test_analytic H w).contDiffAt (test_analytic K w).contDiffAt
  map_smul' c H := iteratedDeriv_fun_const_smul_field c H.val

private def pull (H : Tests) : Module.Dual ℂ Tests →ₗ[ℂ] Module.Dual ℂ Tests where
  toFun L := L.comp (timesTest H)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem jet_of_selector (H K : Tests) (w : ℂ) (n d : ℕ) (c : ℂ)
    (h : ∀ j ≤ n, iteratedDeriv j H.val w = if j = d then c else 0) :
    jet w n (timesTest H K) = n.choose d * c * jet w (n-d) K := by
  change iteratedDeriv n (fun z ↦ H.val z * K.val z) w = _
  rw [iteratedDeriv_fun_mul (test_analytic H w).contDiffAt (test_analytic K w).contDiffAt]
  by_cases hd : d ≤ n
  · rw [Finset.sum_eq_single d]
    · simp [h d hd, jet]
    · intro j hj hne
      simp [h j (by have := Finset.mem_range.mp hj; omega), hne]
    · simp [Finset.mem_range, show d < n+1 by omega]
  · rw [Finset.sum_eq_zero, Nat.choose_eq_zero_of_lt (lt_of_not_ge hd)]
    · simp
    · intro j hj
      have hj' : j ≤ n := by have := Finset.mem_range.mp hj; omega
      simp [h j hj', show j ≠ d by omega]

/-- In an invariant subspace of test functionals, every derivative with a
nonzero coefficient in a finite linear combination of jets of a single entire
generator belongs to the subspace. Only the jets on that finite set enter. -/
private theorem schwartzBergman_finite_jet_isolation (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hGB : ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Set.Icc a b → ‖G z‖ ≤ C)
    (S : Finset ℂ) (m : S → ℕ) (hm : ∀ w, 0 < m w)
    (hord : ∀ w : S, analyticOrderAt G w.val = m w)
    (B : Submodule ℂ (Module.Dual ℂ Tests)) (hB : ∀ H L, L ∈ B → L.comp (timesTest H) ∈ B)
    (c : S → ℕ → ℂ) (hL : (∑ w, ∑ k ∈ Finset.range (m w), c w k • jet w k) ∈ B) :
    ∀ w k, k < m w → c w k ≠ 0 → jet w k ∈ B := by
  classical
  have near (w : S) (d : ℕ) : ∃ H : Tests, (∀ k < m w, iteratedDeriv k H.val w.val = if k = d then 1 else 0) ∧
      ∀ (v : S), w ≠ v → ∀ k < m v, iteratedDeriv k H.val v.val = 0 := by
    obtain ⟨H,hH,hZ⟩ := StripInterpolation.interpolate_transform hG hGB w.val (m w) (hord w)
      (fun i ↦ if i.val = d then 1 else 0)
    refine ⟨H, fun k hk ↦ hH ⟨k,hk⟩, fun v hv ↦ ?_⟩
    apply hZ v.val (fun e ↦ hv (Subtype.ext e.symm)) (m v)
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hG.analyticAt v.val)).mp (hord v).ge
  choose H hH hZ using near
  apply stripBounded_multijets B (fun (w : S) ↦ jet w.val) m (fun w ↦ pull (H w 0)) (fun w ↦ pull (H w 1))
    (fun w L h ↦ hB _ L h) (fun w L h ↦ hB _ L h) _ _ _ c hL
  · intro w v k hk
    ext K
    by_cases e : w = v
    · subst v
      rw [ite_eq_left rfl]
      exact (jet_of_selector _ K w.val k 0 1 (fun j hj ↦ hH w 0 j (hj.trans_lt hk))).trans (by simp)
    · rw [ite_eq_right e]
      exact (jet_of_selector _ K v.val k 0 0 (fun j hj ↦ by simpa using hZ w 0 v e j (hj.trans_lt hk))).trans (by simp)
  · intro w
    ext K
    exact (jet_of_selector _ K w.val 0 1 1 (fun j hj ↦ hH w 1 j (hj.trans_lt (hm w)))).trans (by simp)
  · intro w k hk
    ext K
    exact (jet_of_selector _ K w.val (k+1) 1 1 (fun j hj ↦ hH w 1 j (hj.trans_lt hk))).trans (by simp)

section Synthesis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Finite analytic divisors and a strongly convergent multiplier family detect
the closure using precisely the bounded Taylor functionals annihilating the
whole test ideal. The exceptional finite sets can contain excess generator zeros. -/
private theorem analytic_strip_synthesis
    (N : Submodule ℂ E) (hN : IsClosed (N : Set E)) (i : Tests →ₗ[ℂ] E) (hi : DenseRange i)
    (P : Submodule ℂ Tests) (hP : ∀ (H p : Tests), p ∈ P → timesTest H p ∈ P)
    (act : ∀ H : Tests, ∃ T : E →L[ℂ] E, ∀ p, T (i p) = i (timesTest H p))
    (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hGB : ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Set.Icc a b → ‖G z‖ ≤ C)
    {ι : Type*} (l : Filter ι) [l.NeBot] (U : ι → E →L[ℂ] E) (hlim : ∀ y, Tendsto (fun n ↦ U n y) l (𝓝 y))
    (S : ι → Finset ℂ) (m : (n : ι) → S n → ℕ) (hm : ∀ n w, 0 < m n w)
    (horder : ∀ n w, analyticOrderAt G w.val = m n w)
    (hideal : ∀ n p, (∀ (w : S n) k, k < m n w → iteratedDeriv k p.val w.val = 0) → U n (i p) ∈ N)
    (hcompat : ∀ n p, p ∈ P → U n (i p) ∈ N)
    (y : E) (hy : ∀ (w : ℂ) (k : ℕ) (L : StrongDual ℂ E),
      (∀ p, L (i p) = iteratedDeriv k p.val w) → (∀ p ∈ P, iteratedDeriv k p.val w = 0) → L y = 0) :
    y ∈ N := by
  classical
  let R : StrongDual ℂ E →ₗ[ℂ] Module.Dual ℂ Tests :=
    { toFun L := L.toLinearMap.comp i, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  have hR : Injective R := by
    intro L K e
    apply DFunLike.coe_injective
    refine hi.equalizer L.continuous K.continuous ?_
    funext p
    exact LinearMap.congr_fun e p
  let B := R.range ⊓ P.dualAnnihilator
  have stable (H : Tests) (f : Module.Dual ℂ Tests) (hf : f ∈ B) : f.comp (timesTest H) ∈ B := by
    obtain ⟨T,hT⟩ := act H
    obtain ⟨L,rfl⟩ := hf.1
    constructor
    · exact ⟨L.comp T, LinearMap.ext (fun p ↦ congrArg L (hT p))⟩
    · exact (Submodule.mem_dualAnnihilator _).mpr fun p hp ↦
        (Submodule.mem_dualAnnihilator _).mp hf.2 _ (hP H p hp)
  apply hN.mem_of_tendsto (hlim y)
  refine Eventually.of_forall fun n ↦ ?_
  by_contra hn
  let : IsClosed (N : Set E) := hN
  have hq : N.mkQ (U n y) ≠ 0 := fun h ↦ hn ((Submodule.Quotient.mk_eq_zero N).mp h)
  obtain ⟨g,hg⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hq
  let L := (g.comp N.mkQL).comp (U n)
  have hkill (x : E) (hx : x ∈ N) : g (N.mkQ x) = 0 :=
    (congrArg g ((Submodule.Quotient.mk_eq_zero N).mpr hx)).trans g.map_zero
  let J := (w : S n) × Fin (m n w)
  let D (j : J) := jet j.1.val j.2.val
  have hk : (⨅ j, LinearMap.ker (D j)) ≤ (R L).ker := by
    intro p hp
    exact hkill _ (hideal n p fun w k hk ↦ (Submodule.mem_iInf _).mp hp ⟨w,⟨k,hk⟩⟩)
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (mem_span_of_iInf_ker_le_ker (L := D) hk)
  have hmem : R L ∈ B := ⟨⟨L,rfl⟩, (Submodule.mem_dualAnnihilator _).mpr fun p hp ↦ hkill _ (hcompat n p hp)⟩
  let b (w : S n) (k : ℕ) := if h : k < m n w then c ⟨w,⟨k,h⟩⟩ else 0
  have hsum : ∑ w, ∑ k ∈ Finset.range (m n w), b w k • jet w.val k = ∑ j, c j • D j := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro w _
    rw [← Fin.sum_univ_eq_sum_range (fun k ↦ b w k • jet w.val k)]
    apply Finset.sum_congr rfl
    intro k _
    simp [b,D,k.isLt]
  have hsep := schwartzBergman_finite_jet_isolation G hG hGB (S n) (m n) (hm n) (horder n) B stable b
    ((hsum.trans hc).symm ▸ hmem)
  have hterms (j : J) : ∃ K : StrongDual ℂ E, c j • R K = c j • D j ∧ K y = 0 := by
    by_cases hj : c j = 0
    · exact ⟨0, by simp [hj], by simp⟩
    · have hjet := hsep j.1 j.2 j.2.isLt (by simpa [b,j.2.isLt] using hj)
      obtain ⟨K,hK⟩ := hjet.1
      exact ⟨K, congrArg (c j • ·) hK, hy j.1.val j.2.val K (LinearMap.congr_fun hK)
        ((Submodule.mem_dualAnnihilator _).mp hjet.2)⟩
  choose K hK hz using hterms
  have heq : ∑ j, c j • K j = L := by
    apply hR
    simpa only [map_sum, map_smul, hK] using hc
  apply hg
  change L y = 0
  rw [← heq]
  simp [hz]

end Synthesis
end StripDual

section
open Metric Real
open scoped SchwartzMap
local notation "nuTheta" => canonicalModulatedHaar m𝔽 hm𝔽
local notation "rad(" χ ", " u ")" => (fun x : C𝔽 ↦ ((χ⁻¹ x : Circle) : ℂ) * u (logNorm x))
local instance stripSynthesisCanonicalHaar : (nuTheta : Measure C𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1

/-- The polynomial factor in the translation bound is absorbed by the available
extra width. This gives a weighted L¹ norm for every inverse Mellin kernel. -/
private theorem stripTheta_radial_weight_integrable (J : Set ℝ) (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hzero : 0 ∈ J) (hneg : -(α+s/2) ∈ J) (hpos : α+s/2 ∈ J)
    (p : PositiveRealExponentialDecay J) :
    Integrable (fun t : ℝ ↦ ‖p.val t‖*(max (Real.exp (-α*t)) (Real.exp (α*t))*(1+|t|)^(s/2))) volume := by
  let b := α+s/2
  let P := logExponentialDecayTwist J ⟨b,hpos⟩ p
  let N := logExponentialDecayTwist J ⟨-b,hneg⟩ p
  have hpn (t : ℝ) : ‖P t‖ = Real.exp (b*t)*‖p.val t‖ := by
    rw [show P t = _ from logExponentialDecayTwist_apply J ⟨b,hpos⟩ p t,norm_mul]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have hnn (t : ℝ) : ‖N t‖ = Real.exp (-b*t)*‖p.val t‖ := by
    rw [show N t = _ from logExponentialDecayTwist_apply J ⟨-b,hneg⟩ p t,norm_mul]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have hcont : Continuous p.val := by
    refine (logExponentialDecayTwist J ⟨0,hzero⟩ p).continuous.congr ?_
    intro x
    simpa using logExponentialDecayTwist_apply J ⟨0,hzero⟩ p x
  have hm : Continuous (fun t : ℝ ↦ ‖p.val t‖*(max (Real.exp (-α*t)) (Real.exp (α*t))*(1+|t|)^(s/2))) := by
    have hpow : Continuous (fun t : ℝ ↦ (1+|t|)^(s/2)) := (continuous_const.add continuous_id.abs).rpow_const
      (fun t : ℝ ↦ Or.inl (ne_of_gt (by positivity : 0 < 1+|t|)))
    exact hcont.norm.mul (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).max
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul hpow)
  apply (P.integrable.norm.add N.integrable.norm).mono' hm.aestronglyMeasurable
  filter_upwards with t
  have ht : 0 < 1+|t| := by positivity
  have hL : Real.log (1+|t|) ≤ |t| := by linarith [Real.log_le_sub_one_of_pos ht]
  have hpow : (1+|t|)^(s/2) ≤ Real.exp ((s/2)*|t|) := by
    rw [Real.rpow_def_of_pos ht,Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_right hL (show 0 ≤ s/2 by positivity)]
  have hmax : max (Real.exp (-α*t)) (Real.exp (α*t)) ≤ Real.exp (α*|t|) :=
    max_le (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs t) hα]))
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self t) hα))
  have hm : max (Real.exp (-α*t)) (Real.exp (α*t))*(1+|t|)^(s/2) ≤ Real.exp (b*|t|) := by
    calc
      _ ≤ Real.exp (α*|t|)*Real.exp ((s/2)*|t|) := mul_le_mul hmax hpow (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add]; congr 1; dsimp [b]; ring
  rw [Real.norm_of_nonneg (by positivity),Pi.add_apply,hpn,hnn]
  apply (mul_le_mul_of_nonneg_left hm (norm_nonneg _)).trans
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    nlinarith [mul_nonneg (Real.exp_pos (-b*t)).le (norm_nonneg (p.val t))]
  · rw [abs_of_nonpos ht,show b*(-t) = -b*t by ring]
    nlinarith [mul_nonneg (Real.exp_pos (b*t)).le (norm_nonneg (p.val t))]

private theorem stripTheta_log_integrable {E : Type*} [NormedAddCommGroup E] {p : ℝ → E}
    (hp : Integrable p volume) : Integrable (fun x : C𝔽 ↦ p (logNorm x)) μ𝔽 := by
  have hl := sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have h : Integrable (fun x : C𝔽 ↦ p (logNorm x)) nuTheta := hl.integrable_comp_of_integrable hp
  rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 nuTheta]
  exact h.smul_measure_nnreal

private theorem stripTheta_radial_continuous {J : Set ℝ} (h0 : 0 ∈ J) (χ : PontryaginDual C𝔽)
    (p : PositiveRealExponentialDecay J) : Continuous rad(χ, p.val) := by
  have hc : Continuous p.val := by
    refine (logExponentialDecayTwist J ⟨0,h0⟩ p).continuous.congr ?_
    intro x
    simpa using logExponentialDecayTwist_apply J ⟨0,h0⟩ p x
  have hg : Continuous logNorm := (NNReal.continuous_coe.comp (Units.continuous_val.comp
    (m𝔽).continuous)).log fun x ↦ NNReal.coe_ne_zero.2 (m𝔽 x).ne_zero
  exact (continuous_subtype_val.comp χ⁻¹.continuous).mul (hc.comp hg)

private theorem stripTheta_radial_integrable {J : Set ℝ} (h0 : 0 ∈ J) (χ : PontryaginDual C𝔽)
    (p : PositiveRealExponentialDecay J) : Integrable rad(χ, p.val) μ𝔽 := by
  have hi : Integrable p.val volume := (logExponentialDecayTwist J ⟨0,h0⟩ p).integrable.congr
    (.of_forall fun x ↦ by simpa using logExponentialDecayTwist_apply J ⟨0,h0⟩ p x)
  apply (stripTheta_log_integrable (F := F) hi.norm).mono' (stripTheta_radial_continuous h0 χ p).aestronglyMeasurable
  exact .of_forall fun x ↦ by simp only [norm_mul,Circle.norm_coe,one_mul]; exact le_rfl

private theorem stripTheta_bounded_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c q : ℂ) (hc : ‖c‖ = 1) (T : E →L[ℂ] E) (C : ℝ) (hT : ‖T‖ ≤ C) (u : E) :
    ‖(c*q) • T u‖ ≤ ‖q‖*C*‖u‖ := by
  rw [norm_smul,norm_mul,hc,one_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left ((T.le_opNorm u).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg u))) (norm_nonneg _)

private theorem stripTheta_radial_orbit_integrable {J : Set ℝ} (h0 : 0 ∈ J) (α s : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (hneg : -(α+s/2) ∈ J) (hpos : α+s/2 ∈ J)
    (χ : PontryaginDual C𝔽) (p : PositiveRealExponentialDecay J) (u : W(-α, α, s)) :
    let τ := hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs
    Integrable (fun g ↦ rad(χ, p.val) g • τ g u) μ𝔽 := by
  intro τ
  have hweight := stripTheta_log_integrable (F := F) (stripTheta_radial_weight_integrable J α s hα hs h0 hneg hpos p)
  have ht : Continuous (fun g ↦ τ g u) :=
    (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs).choose_spec.2.comp (Continuous.prodMk_left u)
  apply (hweight.mul_const ‖u‖).mono' ((stripTheta_radial_continuous h0 χ p).smul ht).aestronglyMeasurable
  refine .of_forall fun g ↦ ?_
  exact stripTheta_bounded_smul (χ⁻¹ g : ℂ) (p.val (logNorm g)) (Circle.norm_coe _)
    (τ g) _ (norm_hardySobolevTranslation_le μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs g) u

private theorem stripTheta_orbit_integral (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    {φ : C𝔽 → ℂ} (hi : Integrable φ μ𝔽) (u : W(a, b, s))
    (horb : Integrable (fun g ↦ φ g • hardySobolevTranslation μ𝔽 m𝔽 a b s hab hs g u) μ𝔽) :
    let τ := hardySobolevTranslation μ𝔽 m𝔽 a b s hab hs
    ∀ᵐ x ∂μ𝔽, Integrable (fun g ↦ φ g * u (g⁻¹ * x)) μ𝔽 ∧
      (∫ g, φ g • τ g u ∂μ𝔽) x = lcaConvolution μ𝔽 φ u x := by
  intro τ
  let d (x : C𝔽) := ENNReal.ofReal (intervalSobolevDensity a b s (logNorm x))
  let ν := (μ𝔽).withDensity d
  have hν : ν ≪ μ𝔽 := withDensity_absolutelyContinuous μ𝔽 d
  have hd : Measurable d := by
    have hlog : Measurable (fun x : C𝔽 ↦ Real.log ((m𝔽 x).val : ℝ)) := Real.measurable_log.comp
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).measurable
    have hD : Measurable (intervalSobolevDensity a b s) := by unfold intervalSobolevDensity; fun_prop
    exact (hD.comp hlog).ennreal_ofReal
  have hμ : μ𝔽 ≪ ν := withDensity_absolutelyContinuous' hd.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (mul_pos (lt_max_of_lt_left (Real.exp_pos _))
      (Real.rpow_pos_of_pos (by positivity) _))).ne')
  have : SigmaFinite ν := MeasureTheory.SigmaFinite.withDensity_ofReal _
  have hmeas : AEStronglyMeasurable (fun p : C𝔽 × C𝔽 ↦ φ p.1 * u (p.1⁻¹ * p.2)) ((μ𝔽).prod ν) :=
    hi.1.comp_fst.mul ((Lp.stronglyMeasurable u).comp_measurable
      (measurable_fst.inv.mul measurable_snd)).aestronglyMeasurable
  apply hμ.ae_le
  apply integral_L2_representative horb hmeas
  refine .of_forall fun g ↦ ?_
  filter_upwards [Lp.coeFn_smul (φ g) (τ g u),
    hν.ae_le (hardySobolevTranslation_apply μ𝔽 m𝔽 a b s hab hs g u)] with x hx hy
  rw [hx, Pi.smul_apply, hy, smul_eq_mul]

/-- The physical radial lift is continuous into the Tamagawa weighted strip space. -/
private theorem stripTheta_test_lift (χ : PontryaginDual C𝔽) (α s : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (J : Set ℝ) (hJ : IsOpen J) (hint : OrdConnected J)
    (hsub : Icc (-α) α ⊆ J) :
    ∃ R : PositiveRealExponentialDecay J →L[ℂ] W(-α, α, s),
      ∀ p, (R p : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, p.val) := by
  obtain ⟨R, hR⟩ := stripTail_radial_lift χ hα hs
  obtain ⟨j, _, _, hj⟩ := scalarIntervalSobolev_dense (-α) α s (neg_le_self hα) hs J hJ hint hsub
  refine ⟨R.comp j, fun p ↦ (hR (j p)).trans ?_⟩
  have h := (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽).quasiMeasurePreserving.ae_eq_comp (hj p)
  filter_upwards [(Measure.absolutelyContinuous_isHaarMeasure μ𝔽 nuTheta).ae_eq h] with x hx
  change (χ x : ℂ)⁻¹ * (j p) (logNorm x) = ((χ x)⁻¹ : Circle) * p.val (logNorm x)
  rw [Circle.coe_inv]
  exact congrArg (fun z : ℂ ↦ (χ x : ℂ)⁻¹ * z) hx

private theorem stripTheta_scalar_fourier {J : Set ℝ} (h0 : 0 ∈ J) (χ : PontryaginDual C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (f : PositiveRealExponentialDecay J) (t : ℝ) :
    lcaFourier μ𝔽 rad(χ, f.val) (γ t) =
      ((Measure.haarScalarFactor μ𝔽 nuTheta : ℝ) : ℂ) *
        mellin (fun x ↦ f.val (Real.log x)) ((t : ℂ) * Complex.I) := by
  let ν := nuTheta
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hfun (x : C𝔽) : rad(χ, f.val) x * star (γ t x : ℂ) =
      f.val (logNorm x) * Complex.exp (((t:ℂ)*Complex.I) * (logNorm x : ℂ)) := by
    have hψ : γ t x = (χ x * Circle.exp (t * logNorm x))⁻¹ := by rw [hγ,neg_mul,Circle.exp_neg,mul_inv]
    have hph : star (γ t x : ℂ) = (χ x : ℂ) * Complex.exp (((t * logNorm x : ℝ) : ℂ)*Complex.I) := by
      rw [hψ,Circle.coe_inv_eq_conj, ← Complex.star_def,star_star,Circle.coe_mul,Circle.coe_exp]
    change (((χ x)⁻¹ : Circle) : ℂ) * f.val (logNorm x) * star (γ t x : ℂ) = _
    rw [hph,Circle.coe_inv,Complex.ofReal_mul,show (t:ℂ)*(logNorm x : ℂ)*Complex.I = (t:ℂ)*Complex.I*(logNorm x : ℂ) by ring]
    field_simp [Circle.coe_ne_zero]
  have hprofile := (integral_congr_ae (.of_forall hfun) : lcaFourier μ𝔽 rad(χ, f.val) (γ t) = _)
  refine hprofile.trans ?_
  rw [mellin_logProfile]
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν,integral_smul_nnreal_measure]
  rw [NNReal.smul_def, Complex.real_smul]
  congr 1
  have hl := sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have hc : Continuous f.val := by
    refine (logExponentialDecayTwist J ⟨0,h0⟩ f).continuous.congr ?_
    intro x
    simpa using logExponentialDecayTwist_apply J ⟨0,h0⟩ f x
  let q (x : ℝ) := f.val x * Complex.exp (((t:ℂ)*Complex.I)*(x:ℂ))
  have hq : Continuous q := hc.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  exact (integral_map hl.measurable.aemeasurable (f := q) hq.aestronglyMeasurable).symm.trans
    (congrArg (fun η : Measure ℝ ↦ ∫ x, q x ∂η) hl.map_eq)

/-- A nonzero Fourier coefficient of a radial lift determines its restriction to the compact norm-one group. -/
private theorem stripTheta_fourier_support (χ : PontryaginDual C𝔽) :
    ∃ γ : ℝ → PontryaginDual C𝔽,
      (∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x)) ∧
      ∀ (p : ℝ → ℂ) ψ, ψ ∉ range γ → lcaFourier μ𝔽 rad(χ, p) ψ = 0 := by
  obtain ⟨e, he⟩ := exists_frequency_line m𝔽 hm𝔽 hms𝔽
  let γ (t : ℝ) := χ⁻¹ * (e (Multiplicative.ofAdd (-t))).val
  refine ⟨γ, fun t x ↦ congrArg (fun z ↦ (χ x)⁻¹ * z) (he (-t) x), ?_⟩
  intro p ψ hout
  have hk : ∃ k : C₁, χ k.val ≠ ψ⁻¹ k.val := by
    by_contra! h
    have ha : χ * ψ ∈ lcaAnnihilator (m𝔽).toMonoidHom.ker := by
      apply (mem_lcaAnnihilator_iff ..).mpr
      intro k
      change χ k.val * ψ k.val = 1
      rw [h k]
      exact inv_mul_cancel _
    obtain ⟨u, hu⟩ := e.surjective ⟨χ * ψ, ha⟩
    apply hout
    refine ⟨-u.toAdd, ?_⟩
    change χ⁻¹ * (e (Multiplicative.ofAdd (- -u.toAdd))).val = ψ
    rw [neg_neg]
    change χ⁻¹ * (e u).val = ψ
    rw [hu]
    exact inv_mul_cancel_left _ _
  obtain ⟨k, hk⟩ := hk
  have h := stripProfile_orthogonality μ𝔽 χ ψ⁻¹ k.val hk (fun x ↦ p (logNorm x)) (fun x ↦ by
    change p (Real.log ((m𝔽 (k.val * x)).val : ℝ)) = _
    rw [map_mul, show m𝔽 k.val = 1 from k.property, one_mul]
    rfl)
  refine Eq.trans ?_ h
  apply integral_congr_ae
  refine .of_forall fun x ↦ ?_
  change (((χ x)⁻¹ : Circle) : ℂ) * p (logNorm x) * star (ψ x : ℂ) =
    ((χ x : ℂ)⁻¹ * (((ψ x)⁻¹ : Circle) : ℂ)) * p (logNorm x)
  rw [Circle.coe_inv, Circle.coe_inv_eq_conj, Complex.star_def]
  ring

private theorem stripTheta_radial_symbols {J : Set ℝ} (h0 : 0 ∈ J) (χ : PontryaginDual C𝔽) :
    ∃ γ : ℝ → PontryaginDual C𝔽,
      (∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x)) ∧
      ∀ p : PositiveRealExponentialDecay J,
        (∀ t, lcaFourier μ𝔽 rad(χ, p.val) (γ t) = ((Measure.haarScalarFactor μ𝔽 nuTheta : ℝ) : ℂ) *
          mellin (fun x ↦ p.val (Real.log x)) ((t : ℂ) * Complex.I)) ∧
        ∀ ψ, ψ ∉ range γ → lcaFourier μ𝔽 rad(χ, p.val) ψ = 0 := by
  obtain ⟨γ, hγ, hoff⟩ := stripTheta_fourier_support χ
  exact ⟨γ, hγ, fun p ↦ ⟨stripTheta_scalar_fourier h0 χ γ hγ p, hoff p.val⟩⟩

/-- Weighted closed theta spaces are stable under the actual Bochner integrals
of radial exponential kernels with enough room for the translation norm. -/
private theorem stripTheta_radial_orbit_mem {J : Set ℝ} (h0 : 0 ∈ J) (α s a : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (hneg : -(α+s/2) ∈ J) (hpos : α+s/2 ∈ J)
    (χ : PontryaginDual C𝔽) (p : PositiveRealExponentialDecay J) (u : W(-α, α, s))
    (hu : u ∈ Θ(a, neg_le_self hα, hs)) :
    let τ := hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs
    (∫ g, rad(χ, p.val) g • τ g u ∂μ𝔽) ∈ Θ(a, neg_le_self hα, hs) := by
  intro τ
  let K := Θ(a, neg_le_self hα, hs)
  obtain ⟨ρ,hρ,-,-⟩ := exists_globalThetaSobolevAction (F := F) a (neg_le_self hα) hs
  have hτ (g : C𝔽) : ∀ v ∈ K, τ g v ∈ K := fun v hv ↦ (hρ g ⟨v,hv⟩) ▸ (ρ g ⟨v,hv⟩).property
  let : IsClosed (K : Set W(-α, α, s)) := Submodule.isClosed_topologicalClosure _
  apply (Submodule.Quotient.mk_eq_zero K).mp
  change K.mkQL (∫ g, rad(χ, p.val) g • τ g u ∂μ𝔽) = 0
  rw [← K.mkQL.integral_comp_comm (stripTheta_radial_orbit_integrable h0 α s hα hs hneg hpos χ p u)]
  exact integral_eq_zero_of_ae (.of_forall fun g ↦
    (Submodule.Quotient.mk_eq_zero K).mpr (K.smul_mem _ (hτ g u hu)))

private theorem stripTheta_eq_of_fourier {l r s : ℝ} (u v : W(l, r, s)) (hu : Integrable (u : C𝔽 → ℂ) μ𝔽)
    (hv : Integrable (v : C𝔽 → ℂ) μ𝔽) (h : ∀ ψ, lcaFourier μ𝔽 u ψ = lcaFourier μ𝔽 v ψ) : u = v := by
  let H := lcaFourier_L1 μ𝔽
  let f : Lp ℂ 1 μ𝔽 := hu.toL1 u
  let g : Lp ℂ 1 μ𝔽 := hv.toL1 v
  have hf : (f : C𝔽 → ℂ) =ᵐ[μ𝔽] (u : C𝔽 → ℂ) := hu.coeFn_toL1
  have hg : (g : C𝔽 → ℂ) =ᵐ[μ𝔽] (v : C𝔽 → ℂ) := hv.coeFn_toL1
  have hfg : H.choose f = H.choose g := by
    apply ZeroAtInftyContinuousMap.ext
    intro ψ
    rw [H.choose_spec.1 f ψ, H.choose_spec.1 g ψ]
    exact (integral_congr_ae (hf.mul EventuallyEq.rfl)).trans
      ((h ψ).trans (integral_congr_ae (hg.symm.mul EventuallyEq.rfl)))
  have hfg' : f = g := H.choose_spec.2.1 hfg
  have hrep : (f : C𝔽 → ℂ) =ᵐ[μ𝔽] (g : C𝔽 → ℂ) := by rw [hfg']
  exact Lp.ext ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq (hf.symm.trans (hrep.trans hg)))

/-- On the normalized line the ordinary Fourier transform of the centered theta
representative is its global theta Mellin transform, evaluated at the shifted center. -/
private theorem stripTheta_weighted_fourier (χ : PontryaginDual C𝔽) (a : ℝ)
    (γ : ℝ → PontryaginDual C𝔽) (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (f : adelePolarSubspace F) :
    Integrable (modulationWeight m𝔽 a (adelicTheta f.val)) μ𝔽 ∧ ∀ t,
      lcaFourier μ𝔽 (modulationWeight m𝔽 a (adelicTheta f.val)) (γ t) =
      globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a, t))) := by
  obtain ⟨hf,hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hw (g : C𝔽) :
      adelicTheta f.val g * (ideleClassNormTwist (1 : PontryaginDual C𝔽) (a : ℂ)) g =
      modulationWeight m𝔽 a (adelicTheta f.val) g := by
    have hp : 0 < ((m𝔽 g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    change _ * ((1 : ℂ) * (((m𝔽 g).val : ℝ) : ℂ) ^ (a : ℂ)) = ((((m𝔽 g).val : ℝ) ^ a : ℝ) : ℂ) * _
    rw [one_mul, ← Complex.ofReal_cpow hp.le]
    exact mul_comm _ _
  refine ⟨(globalThetaMellinIntegral_integrable_of_vanishing f.val hf hf' _).congr (.of_forall hw), fun t ↦ ?_⟩
  apply integral_congr_ae
  refine .of_forall fun g ↦ ?_
  have hp : 0 < ((m𝔽 g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hψ : γ t g = (χ g * Circle.exp (t * logNorm g))⁻¹ := by
    rw [hγ, neg_mul, Circle.exp_neg, mul_inv]
  have hph : star (γ t g : ℂ) = (χ g : ℂ) * Complex.exp (((t * logNorm g : ℝ) : ℂ) * Complex.I) := by
    rw [hψ, Circle.coe_inv_eq_conj, ← Complex.star_def, star_star, Circle.coe_mul, Circle.coe_exp]
  change modulationWeight m𝔽 a (adelicTheta f.val) g * star (γ t g : ℂ) = _
  rw [hph]
  change (((((m𝔽 g).val : ℝ) ^ a : ℝ) : ℂ) * adelicTheta f.val g) * _ =
    adelicTheta f.val g * ((χ g : ℂ) * ((((m𝔽 g).val : ℝ) : ℂ) ^ (shift(a, t))))
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le,
    Real.rpow_def_of_pos hp, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_mul,
    mul_add, Complex.exp_add]
  rw [show (t : ℂ) * (logNorm g : ℂ) * Complex.I = (logNorm g : ℂ) * ((t : ℂ) * Complex.I) by ring]
  ring_nf
  rfl

/-- A Mellin product by the centered transform of any adelic polar-free test
is the Fourier transform of its radial convolution in the closed theta space. -/
private theorem stripTheta_generator_product_mem {J : Set ℝ} (h0 : 0 ∈ J) (α s a : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (hneg : -(α+s/2) ∈ J) (hpos : α+s/2 ∈ J)
    (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F) (p : PositiveRealExponentialDecay J)
    (v : W(-α, α, s)) (w : PositiveRealExponentialDecay J) (hv : (v : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, w.val))
    (hprod : ∀ t : ℝ, mellin (fun x ↦ w.val (Real.log x)) ((t:ℂ)*Complex.I) =
      globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a:ℂ)+(t:ℂ)*Complex.I)) *
        mellin (fun x ↦ p.val (Real.log x)) ((t:ℂ)*Complex.I)) :
    v ∈ Θ(a, neg_le_self hα, hs) := by
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (neg_le_self hα) hs).exists.choose
  let u := E (Submodule.Quotient.mk f)
  let τ := hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs
  let φ := rad(χ, p.val)
  let z := ∫ g, φ g • τ g u ∂μ𝔽
  have hu := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (neg_le_self hα) hs).exists.choose_spec.2 f
  obtain ⟨γ,hγ,hFT⟩ := stripTheta_radial_symbols h0 χ
  have hG := stripTheta_weighted_fourier χ a γ hγ f
  have huI : Integrable (u : C𝔽 → ℂ) μ𝔽 := hG.1.congr hu.symm
  have huF (t : ℝ) : lcaFourier μ𝔽 u (γ t) =
      globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a:ℂ)+(t:ℂ)*Complex.I)) :=
    (integral_congr_ae (hu.mul EventuallyEq.rfl)).trans (hG.2 t)
  have hφ : Integrable φ μ𝔽 := stripTheta_radial_integrable h0 χ p
  have horb := stripTheta_radial_orbit_integrable h0 α s hα hs hneg hpos χ p u
  have hz : (z : C𝔽 → ℂ) =ᵐ[μ𝔽] lcaConvolution μ𝔽 φ u :=
    (stripTheta_orbit_integral (-α) α s (neg_le_self hα) hs hφ u horb).mono fun _ h ↦ h.2
  have hzi := (lcaConvolution_integrable μ𝔽 hφ huI).2.1.congr hz.symm
  have hvi := (stripTheta_radial_integrable h0 χ w).congr hv.symm
  have hconv := lcaFourier_convolution μ𝔽 hφ huI
  have heq : z = v := by
    apply stripTheta_eq_of_fourier (F := F) (l := -α) (r := α) (s := s) z v hzi hvi
    intro ψ
    refine (integral_congr_ae (hz.mul EventuallyEq.rfl)).trans ((congrFun hconv ψ).trans ?_)
    refine Eq.trans (b := lcaFourier μ𝔽 rad(χ, w.val) ψ) ?_ (integral_congr_ae (hv.symm.mul EventuallyEq.rfl))
    change lcaFourier μ𝔽 rad(χ, p.val) ψ*lcaFourier μ𝔽 u ψ = _
    by_cases hψ : ψ ∈ range γ
    · obtain ⟨t,rfl⟩ := hψ
      rw [(hFT p).1,huF,(hFT w).1,hprod]
      ring
    · rw [(hFT p).2 _ hψ,zero_mul,(hFT w).2 _ hψ]
  rw [←heq]
  exact stripTheta_radial_orbit_mem h0 α s a hα hs hneg hpos χ p u
    (Submodule.le_topologicalClosure _ (LinearMap.mem_range_self E.toLinearMap _))

open Real
/-- Some polar-free theta test has a transform nonzero at absolute real coordinate two. -/
private theorem exists_stripTheta_generator_nonzero (χ : PontryaginDual C𝔽) :
    ∃ f : adelePolarSubspace F, globalThetaMellinIntegral f.val (ideleClassNormTwist χ 2) ≠ 0 := by
  have h₂ := continuedCompletedHeckeL_order_at_two_nonpos χ
  obtain ⟨f,hf⟩ := (isLeast_globalThetaMellinIntegral_orders χ (2:ℂ)).1
  obtain ⟨h₀,h₁⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hG := globalThetaMellinIntegral_entire_of_vanishing f.val h₀ h₁ χ
  exact ⟨f,(hG.analyticAt _).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp (hf.trans (max_eq_left h₂))⟩

/-- Mellin values on the strip determine every logarithmic test profile. -/
private theorem stripTheta_mellin_ext {J : Set ℝ} (hJ : IsOpen J) (hi : OrdConnected J) (hn : J.Nonempty)
    (p q : PositiveRealExponentialDecay J)
    (hpq : ∀ z : ℂ, z.re ∈ J → mellin (fun t ↦ p.val (Real.log t)) z = mellin (fun t ↦ q.val (Real.log t)) z) :
    p = q := by
  let M := positiveRealFourierMellin J hJ hi hn
  apply M.injective
  apply Subtype.ext
  funext z
  by_cases hz : z.re ∈ J
  · exact (positiveRealFourierMellin_apply J hJ hi hn p z hz).trans ((hpq z hz).trans
      (positiveRealFourierMellin_apply J hJ hi hn q z hz).symm)
  · exact ((M p).property.1 hz).trans ((M q).property.1 hz).symm

/-- For one polar-free generator, a normalized Blaschke tail of its full divisor
times any entire rapidly decreasing test killing the complementary finite jets
has a radial lift in the closed global theta Sobolev space. -/
private theorem stripTheta_full_divisor_finite_jet_mem (χ : PontryaginDual C𝔽) (f : adelePolarSubspace F)
    (α s a A k c r : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (hr : α+s/2 < r)
    (hk : 0 < k) (hkc : k < c) (hwide : k*(|0-A|+r) < Real.pi/2) (hcr : c*r < Real.pi/2)
    (h₀ : globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a:ℂ)+(A:ℂ))) ≠ 0) :
    let G (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a:ℂ)+z))
    let D := stripBlaschkeFromDisk (A:ℂ) k
    let B := stripBlaschkeToDisk (A:ℂ) k
    let Z := {z : ℂ // z ∈ ball 0 1 ∧ G (D z) = 0}
    let m (i : Z) := analyticOrderNatAt G (D i.val)
    let J := Ioo (-r) r
    ∀ (S : Finset Z) (H : SchwartzBergman (univ : Set ℝ)),
      (∀ i ∈ S, (m i : ℕ∞) ≤ analyticOrderAt H.val (D i.val)) →
      ∃ y : PositiveRealExponentialDecay J,
        (∀ z : ℂ, z.re ∈ J → mellin (fun x ↦ y.val (Real.log x)) z =
          Blaschke.tail (fun i : Z ↦ i.val) m S (B z)*H.val z) ∧
        (∃ v : W(-α, α, s), (v : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, y.val) ∧ v ∈ Θ(a, neg_le_self hα, hs)) ∧
        ∀ (q : PositiveRealExponentialDecay J) (v : W(-α, α, s)),
          (∀ z : ℂ, z.re ∈ J → mellin (fun x ↦ q.val (Real.log x)) z =
            Blaschke.tail (fun i : Z ↦ i.val) m S (B z)*H.val z) →
          (v : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, q.val) → v ∈ Θ(a, neg_le_self hα, hs) := by
  intro G D B Z m J S H hmem
  obtain ⟨hG, hGB⟩ := stripProfile_theta_strip_bound χ f a
  let R := (Real.pi / 2) / k
  have hR : 0 < R := div_pos (by positivity) hk
  obtain ⟨M, hM⟩ := hGB (A - R) (A + R) (by linarith)
  have hb (z : ℂ) (hz : |z.re - A| < R) : ‖G z‖ ≤ M := by
    apply hM
    exact ⟨by linarith [(abs_lt.mp hz).1], by linarith [(abs_lt.mp hz).2]⟩
  have hr' : 0 < r := by linarith
  obtain ⟨y,hy,K,v,hvy,hv⟩ := stripBergman_single_generator_finite_jets A k c r hk hkc hr' hwide hcr G
    (fun z _ ↦ hG.analyticAt z) h₀ M hb S H hmem
  have hsub : Icc (-α) α ⊆ J := fun t ht ↦ ⟨by linarith [ht.1],by linarith [ht.2]⟩
  obtain ⟨L,hL⟩ := stripTheta_test_lift χ α s hα hs J isOpen_Ioo ordConnected_Ioo hsub
  have hzero : 0 ∈ J := ⟨by linarith,hr'⟩
  have hneg : -(α+s/2) ∈ J := ⟨by linarith,by linarith⟩
  have hpos : α+s/2 ∈ J := ⟨by linarith,hr⟩
  have hn (n : ℕ) : L (v n) ∈ Θ(a, neg_le_self hα, hs) := by
    apply stripTheta_generator_product_mem hzero α s a hα hs hneg hpos χ f (K n) _ (v n) (hL _)
    intro t
    apply hv n
    simpa using hr'
  have hclosed : IsClosed (Θ(a, neg_le_self hα, hs) : Set W(-α, α, s)) := Submodule.isClosed_topologicalClosure _
  have hym : L y ∈ Θ(a, neg_le_self hα, hs) :=
    hclosed.mem_of_tendsto ((L.continuous.tendsto y).comp hvy) (.of_forall hn)
  refine ⟨y,hy,⟨L y,hL y,hym⟩,fun q u hq hu ↦ ?_⟩
  have hqy : q = y := stripTheta_mellin_ext isOpen_Ioo ordConnected_Ioo ⟨0,hzero⟩ q y
    (fun z hz ↦ (hq z hz).trans (hy z hz).symm)
  subst q
  have heq : u = L y := Lp.ext ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq (hu.trans (hL y).symm))
  exact heq ▸ hym

end

section
local notation "Ws(" α ", " s ")" => CompactIntervalSobolev volume id (-α) α s
local notation "uJet(" χ ", " hα ", " hs ", " j ")" =>
  (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))
open scoped Classical

/-- An admitted jet on an inverse Hecke-character component agrees with its
bounded scalar Mellin derivative on the entire radial Sobolev space. The
Tamagawa/canonical Haar factor is explicit. All other angular components vanish. -/
private theorem spectralStripJet_pairing_radial_eval
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (ω : PontryaginDual C₁)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (j : SpectralStripJetIndex χ a α s)
    (K : Ws(α, s) →L[ℂ] W(-α, α, s))
    (hK : ∀ f, (K f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * f (logNorm x))
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hlog : MeasurePreserving logNorm ν volume)
    (Λ : Ws(α, s) →L[ℂ] ℂ)
    (hΛ : ∀ (p : PositiveRealExponentialDecay univ) (f : Ws(α, s)),
      (f : ℝ → ℂ) =ᵐ[volume] p.val →
        Λ f = iteratedDeriv j.val.2.2.2 (mellin (fun t ↦ p.val (Real.log t))) ((j.val.2.1 : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I)) :
    ∀ f, spectralSobolevPairing (K f) (uJet(χ, hα, hs, j)) =
      if j.val.1 = ω then ((Measure.haarScalarFactor μ𝔽 ν : ℝ) : ℂ) *
        Λ f else 0 := by
  let c : ℂ := ((Measure.haarScalarFactor μ𝔽 ν : ℝ) : ℂ)
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (neg_le_self hα) hs).exists.choose
  let u := uJet(χ, hα, hs, j)
  let e := T.symm u
  have he (y : W(-α, α, s)) : spectralSobolevPairing y u = e y :=
    ((spectralSobolevPairing_dual (neg_le_self hα) hs e y).2.trans
      (congrArg (spectralSobolevPairing y) (T.apply_symm_apply u))).symm
  have hc : Continuous fun f : Ws(α, s) ↦ spectralSobolevPairing (K f) u := by
    simp only [he]
    exact e.continuous.comp K.continuous
  have hright : Continuous (fun f : Ws(α, s) ↦ if j.val.1 = ω then c * Λ f else 0) := by
    by_cases h : j.val.1 = ω
    · simp only [ite_eq_left h]
      fun_prop
    · simp only [ite_eq_right h]
      exact continuous_const
  obtain ⟨P, -, hd, hP⟩ := scalarIntervalSobolev_dense (-α) α s (neg_le_self hα) hs univ
    isOpen_univ ordConnected_univ (subset_univ _)
  intro f
  change spectralSobolevPairing (K f) u = if j.val.1 = ω then c * Λ f else 0
  refine hd.induction_on f (isClosed_eq hc hright) (fun p ↦ ?_)
  have ht := hlog.quasiMeasurePreserving.ae_eq_comp (hP p)
  have hp : (K (P p) : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * p.val (logNorm x) := by
    refine (hK _).trans ?_
    apply (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 ν).ae_eq
    filter_upwards [ht] with x hx using congrArg ((χ ω x : ℂ)⁻¹ * ·) hx
  change spectralSobolevPairing (K (P p)) (uJet(χ, hα, hs, j)) = _
  rw [stripTail_profile_pairing χ hχ ω hα hs isOpen_univ (subset_univ _) ν
    hlog p (K (P p)) hp j, hΛ p (P p) (hP p)]

end

namespace SharpStripEval

/-- For a zero of multiplicity `N`, the exact strip index is equivalent to a
derivative below `N` extending continuously to the scalar Sobolev space. -/
private theorem lt_spectralStripMultiplicity_iff_bounded_eval (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (N k : ℕ) (z : ℂ) :
    k < spectralStripMultiplicity α s z.re N ↔ k < N ∧
      ∃ Λ : CompactIntervalSobolev volume id (-α) α s →L[ℂ] ℂ,
        ∀ (f : PositiveRealExponentialDecay univ) (u : CompactIntervalSobolev volume id (-α) α s),
          (u : ℝ → ℂ) =ᵐ[volume] f.val →
          Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z := by
  rw [scalarIntervalSobolev_eval_iff α s hα hs k z]
  have he : (z.re = -α ∨ z.re = α) ↔ |z.re| = α := by
    rcases le_total 0 z.re with hz | hz
    · rw [abs_of_nonneg hz]
      constructor
      · rintro (h | h) <;> linarith
      · exact Or.inr
    · rw [abs_of_nonpos hz]
      constructor
      · rintro (h | h) <;> linarith
      · exact fun h ↦ Or.inl (by linarith)
  by_cases hi : |z.re| < α
  · rw [spectralStripMultiplicity_interior (abs_lt.mp hi) s N]
    simp [hi]
  · by_cases hedge : |z.re| = α
    · rw [spectralStripMultiplicity_boundary hα (he.mpr hedge) s N, lt_spectralBoundaryMultiplicity]
      simp only [hedge, lt_self_iff_false, false_or, true_and]
      exact and_congr_right fun _ ↦ by constructor <;> intro h <;> linarith
    · have hni : ¬ (-α < z.re ∧ z.re < α) := fun h ↦ hi (abs_lt.mpr h)
      have hne : ¬ (z.re = -α ∨ z.re = α) := fun h ↦ hedge (he.mp h)
      simp [spectralStripMultiplicity, hni, hne, hi, hedge]

end SharpStripEval

section
open scoped SchwartzMap
local notation "nuTheta" => canonicalModulatedHaar m𝔽 hm𝔽
local notation "rad(" χ ", " u ")" => (fun x : C𝔽 ↦ ((χ⁻¹ x : Circle) : ℂ) * u (logNorm x))
local instance stripComponentCanonicalHaar : (nuTheta : Measure C𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
local notation "Ws(" α ", " s ")" => CompactIntervalSobolev volume id (-α) α s
local notation "uJet(" χ ", " hα ", " hs ", " j ")" =>
  (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))

/-- Compact character averaging takes each pure vector back onto its character
component. Totality extends this observation from pure vectors to all vectors. -/
private theorem stripAngular_compact_assembly {G E J : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (κ : Measure G) [κ.IsHaarMeasure] [κ.WeaklyRegular] (τ : G →* (E →L[ℂ] E))
    (hτ : Continuous (fun p : G × E ↦ τ p.1 p.2))
    (R : PontryaginDual G → Submodule ℂ E) (hR : ∀ ξ, IsClosed (R ξ : Set E))
    (hE : ∀ ξ (x : E), x ∈ R ξ → ∀ g, τ g x = (ξ g : ℂ) • x)
    (htotal : ∀ (V : Submodule ℂ E), IsClosed (V : Set E) → (∀ ξ, R ξ ≤ V) → ∀ x, x ∈ V)
    (ω : J → PontryaginDual G) (Λ : J → StrongDual ℂ E)
    (heigen : ∀ j g x, Λ j (τ g x) = (ω j g : ℂ)*Λ j x)
    (N : Submodule ℂ E) (hN : IsClosed (N : Set E))
    (hRker : ∀ ξ (x : E), x ∈ R ξ → (∀ j, ω j = ξ → Λ j x = 0) → x ∈ N)
    (y : E) (hy : ∀ j, Λ j y = 0) : y ∈ N := by
  classical
  by_contra hny
  obtain ⟨φ,hne,hzero⟩ := exists_dual_eq_zero_on_submodule_of_notMem N hN hny
  let u (g : G) := φ (τ g y)
  have hu : Continuous u := φ.continuous.comp (hτ.comp (continuous_id.prodMk continuous_const))
  have hcoeff (ξ : PontryaginDual G) : ∫ g, star (ξ g : ℂ)*u g ∂κ = 0 := by
    let : NormedSpace ℝ E := NormedSpace.complexToReal
    have hborn (p : Seminorm ℂ E)
        (hp : ∀ B : Set E, Bornology.IsVonNBounded ℂ B → BddAbove (p '' B)) : Continuous p := by
      obtain ⟨M, hM⟩ := hp _ (NormedSpace.isVonNBounded_closedBall ℂ E 1)
      apply p.continuous' (r := max M 0 + 1)
      apply Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : E) zero_lt_one)
      intro x hx
      rw [Seminorm.mem_closedBall_zero]
      exact (hM ⟨x, hx, rfl⟩).trans ((le_max_left M 0).trans (lt_add_one _).le)
    obtain ⟨P, hP⟩ := (existsUnique_compactActionIsotypicAverage κ τ hτ hborn
      (existsUnique_spectralLineTestCompletion_uniform (fun g x ↦ τ g x) hτ) ξ).exists
    have hsum (x : E) (δ : StrongDual ℂ E) :
        δ (P x) = ∫ g, star (ξ g : ℂ) * δ (τ g x) ∂κ := by
      obtain ⟨_, he⟩ := hP x
      have h := congrArg (fun z : PettisWeakCompletion E ↦
        (show Module.Dual ℂ (StrongDual ℂ E) from z) δ) he
      change δ (P x) = ∫ g, δ (star (ξ g : ℂ) • τ g x) ∂κ.restrict univ at h
      simpa only [Measure.restrict_univ, map_smul, smul_eq_mul] using h
    have hproj (θ : PontryaginDual G) (x : E) (hx : x ∈ R θ) :
        P x = (if ξ = θ then (κ.real univ : ℂ) else 0) • x := by
      apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
      intro δ
      rw [hsum, map_smul,smul_eq_mul,←integral_character_pair κ ξ θ,←integral_mul_const]
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      rw [hE θ x hx g,map_smul,smul_eq_mul,mul_assoc]
    have hPx (x : E) : P x ∈ R ξ := by
      apply htotal ((R ξ).comap P.toLinearMap) ((hR ξ).preimage P.continuous) _ x
      intro θ w hw
      change P w ∈ R ξ
      rw [hproj θ w hw]
      split_ifs with h
      · exact (R ξ).smul_mem _ (h ▸ hw)
      · rw [zero_smul]; exact (R ξ).zero_mem
    have hPy := hRker ξ (P y) (hPx y) (fun j _ ↦ by
      rw [hsum]
      exact integral_eq_zero_of_ae (.of_forall fun g ↦ by
        change star (ξ g : ℂ)*Λ j (τ g y) = 0
        rw [heigen,hy,mul_zero,mul_zero]))
    exact (hsum y φ).symm.trans (hzero _ hPy)
  have he := ae_eq_zero_of_character_integral_eq_zero κ (hu.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hcoeff
  have heq := Measure.eq_of_ae_eq he hu continuous_const
  exact hne (by simpa [u] using congrFun heq 1)

/-- The canonical log pullback is an isometry even after multiplication by an
arbitrary unitary character; changing Haar normalization preserves closed range. -/
private theorem stripAngular_closed_radial (ξ : PontryaginDual C𝔽) (α s : ℝ) :
    ∃ L : Ws(α, s) →L[ℂ] W(-α, α, s), IsClosed (range L) ∧
      ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (ξ x : ℂ)⁻¹ * f (logNorm x) := by
  let ρ := intervalSobolevDensity (-α) α s
  let η := volume.withDensity (fun t : ℝ ↦ ENNReal.ofReal (ρ t))
  let ν := nuTheta
  let μw := ν.withDensity (fun x : C𝔽 ↦ ENNReal.ofReal (ρ (logNorm x)))
  have hρ : Continuous ρ := continuous_intervalSobolevDensity' _ _ _
  have hl : MeasurePreserving logNorm ν (volume : Measure ℝ) := sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have hw : MeasurePreserving logNorm μw η := by
    refine ⟨hl.measurable,?_⟩
    ext X hX
    rw [Measure.map_apply hl.measurable hX,withDensity_apply _ (hl.measurable hX),withDensity_apply _ hX]
    exact hl.setLIntegral_comp_preimage hX hρ.measurable.ennreal_ofReal
  let v (x : C𝔽) := (ξ x : ℂ)⁻¹
  have hv : Continuous v := (continuous_subtype_val.comp ξ.continuous).inv₀ fun x ↦ Circle.coe_ne_zero _
  have hvn (x : C𝔽) : ‖v x‖ = 1 := by simp [v]
  obtain ⟨U,hU⟩ := sobolev_unitary_mul μw v hv.measurable hvn
  let T := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ logNorm hw
  let V := U.comp T.toContinuousLinearMap
  have hUV (f : Lp ℂ 2 η) : ‖V f‖ = ‖f‖ := by
    have he : ‖U (T f)‖ = ‖T f‖ := by
      rw [Lp.norm_def,Lp.norm_def]
      apply congrArg ENNReal.toReal
      apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
      filter_upwards [hU (T f)] with x hx
      rw [hx,norm_mul,hvn,one_mul]
    exact he.trans (T.norm_map f)
  let I : Lp ℂ 2 η →ₗᵢ[ℂ] Lp ℂ 2 μw := {V.toLinearMap with norm_map' := hUV}
  have hclosed : IsClosed (range V) := I.isometry.isClosedEmbedding.isClosed_range
  let E := globalThetaAmbient_equiv_canonical (F := F) hm𝔽 (-α) α s
  let B := E.choose
  let L : Ws(α, s) →L[ℂ] W(-α, α, s) := B.symm.toContinuousLinearMap.comp V
  have hBV (f : Ws(α, s)) : B (L f) = V f := B.apply_symm_apply _
  have heq : range L = B ⁻¹' range V := by
    ext y
    constructor
    · rintro ⟨f,rfl⟩
      exact ⟨f,(hBV f).symm⟩
    · rintro ⟨f,hf⟩
      exact ⟨f,B.injective ((hBV f).trans hf)⟩
  refine ⟨L, heq ▸ hclosed.preimage B.continuous,fun f ↦ ?_⟩
  have habs : ν ≪ μw := withDensity_absolutelyContinuous' (hρ.measurable.comp hl.measurable).ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (intervalSobolevDensity_pos _ _ _ _)).ne')
  have hBrep := (E.choose_spec (L f)).1.symm
  rw [show E.choose (L f) = V f from hBV f] at hBrep
  apply hBrep.trans
  apply (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 nuTheta).ae_eq
  apply habs.ae_eq
  filter_upwards [hU (T f), Lp.coeFn_compMeasurePreserving (f : Lp ℂ 2 η) hw] with x h₁ h₂
  exact h₁.trans (congrArg (v x * ·) h₂)

private theorem stripAngular_radial_eigen (χ : PontryaginDual C𝔽) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (f : Ws(α, s)) (y : W(-α, α, s))
    (hy : (y : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ x : ℂ)⁻¹ * f (logNorm x)) (k : C₁) :
    hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs k.val y = (χ k.val : ℂ) • y := by
  have ha : μ𝔽 ≪ (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (logNorm x))) :=
    withDensity_absolutelyContinuous' (((continuous_intervalSobolevDensity' (-α) α s).measurable.comp
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).measurable.log).ennreal_ofReal.aemeasurable)
      (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (intervalSobolevDensity_pos _ _ _ _)).ne')
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
  have hsml := ha.ae_eq (Lp.coeFn_smul (χ k.val : ℂ) y)
  have hpre := (measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving.ae_eq_comp hy
  filter_upwards [hardySobolevTranslation_apply μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs k.val y,hpre,hy,hsml] with x h₁ h₂ h₃ h₄
  refine h₁.trans (h₂.trans (h₄.symm ▸ ?_))
  change (χ (k.val⁻¹*x) : ℂ)⁻¹ * f (logNorm (k.val⁻¹*x)) = (χ k.val : ℂ) * y x
  have hM : ideleClassNorm F (k.val⁻¹*x) = ideleClassNorm F x := by rw [map_mul,map_inv,k.property,inv_one,one_mul]
  change (χ (k.val⁻¹*x) : ℂ)⁻¹ * f (Real.log (((ideleClassNorm F (k.val⁻¹*x)).val):ℝ)) = _
  rw [hM,h₃,map_mul,map_inv,Circle.coe_mul,Circle.coe_inv,mul_inv_rev,inv_inv]
  ring

private theorem stripAngular_raw_normOne (χ : PontryaginDual C𝔽) (b t : ℝ) (n : ℕ) (g : C₁) (x : C𝔽) :
    spectralZeroJet χ b t n (g.val*x) = (χ g.val : ℂ) * spectralZeroJet χ b t n x := by
  have hm : ideleClassNorm F (g.val*x) = ideleClassNorm F x := by rw [map_mul,g.property,one_mul]
  have hl : logNorm (g.val*x) = logNorm x := congrArg (fun z : ℝ≥0ˣ ↦ Real.log (z.val : ℝ)) hm
  rw [stripProfile_jet,stripProfile_jet,hl,map_mul,Circle.coe_mul]
  ring

private theorem stripAngular_integral_eigen {G : Type*} [CommGroup G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (r f : G → ℂ) (g : G) (c : ℂ)
    (hr : ∀ x, r (g*x) = c*r x) :
    (∫ x, f (g⁻¹*x)*r x ∂μ) = c*∫ x, f x*r x ∂μ := by
  rw [← integral_const_mul]
  refine (integral_mul_left_eq_self (μ := μ) (fun x ↦ f (g⁻¹*x)*r x) g).symm.trans ?_
  apply integral_congr_ae
  refine .of_forall fun x ↦ ?_
  change f (g⁻¹*(g*x))*r (g*x) = c*(f x*r x)
  rw [inv_mul_cancel_left,hr]
  ring

private theorem stripAngular_jet_normOne_dual (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (j : SpectralStripJetIndex χ a α s) :
    ∃ Λ : StrongDual ℂ W(-α, α, s),
      (∀ u, Λ u = spectralSobolevPairing u (uJet(χ, hα, hs, j))) ∧
      ∀ (g : C₁) u, Λ (hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs g.val u) = (j.val.1 g : ℂ)*Λ u := by
  let v : W'(-α, α, s) := uJet(χ, hα, hs, j)
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (neg_le_self hα) hs).exists.choose
  let Λ := T.symm v
  have hp (y : W(-α, α, s)) : Λ y = spectralSobolevPairing y v :=
    (spectralSobolevPairing_dual (neg_le_self hα) hs Λ y).2.trans (congrArg (spectralSobolevPairing y) (T.apply_symm_apply v))
  have habs : μ𝔽 ≪ L2μ'(-α, α, s) :=
    withDensity_absolutelyContinuous' (symmIntervalSobolevDensity_inv_continuous hα s).measurable.ennreal_ofReal.aemeasurable
      (.of_forall fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (symmIntervalSobolevDensity_pos hα s (logNorm g))))
  have hrep : (v : C𝔽 → ℂ) =ᵐ[μ𝔽] stripJet(χ, j) := habs.ae_le (MemLp.coeFn_toLp _)
  have hΛ (y : W(-α, α, s)) : Λ y = ∫ x, y x*stripJet(χ, j) x ∂μ𝔽 := (hp y).trans (integral_congr_ae (EventuallyEq.rfl.mul hrep))
  refine ⟨Λ,hp,fun g y ↦ ?_⟩
  rw [hΛ,hΛ]
  have he : χ j.val.1 g.val = j.val.1 g := DFunLike.congr_fun (hχ _) g
  rw [←he]
  have htr := hardySobolevTranslation_apply μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs g.val y
  exact (integral_congr_ae (htr.mul EventuallyEq.rfl)).trans
    (stripAngular_integral_eigen μ𝔽 (stripJet(χ, j)) y g.val _ (stripAngular_raw_normOne _ _ _ _ g))

/-- The reverse common-kernel inclusion on a strip follows from its matching
admitted moments for each inverse-character radial Sobolev vector. -/
private theorem spectralStripJet_reverse_of_radial_lifts (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hpure : ∀ (ω : PontryaginDual C₁) (f : Ws(α, s)) (v : W(-α, α, s)),
      ((v : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * f (logNorm x)) →
      (∀ j : SpectralStripJetIndex χ a α s, j.val.1 = ω → spectralSobolevPairing v (uJet(χ, hα, hs, j)) = 0) →
      v ∈ Θ(a, neg_le_self hα, hs))
    (y : W(-α, α, s)) (hy : ∀ j : SpectralStripJetIndex χ a α s, spectralSobolevPairing y (uJet(χ, hα, hs, j)) = 0) :
    y ∈ Θ(a, neg_le_self hα, hs) := by
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let κ : Measure C₁ := Measure.haar
  let : κ.IsHaarMeasure := inferInstanceAs (Measure.haar (G := C₁)).IsHaarMeasure
  let τ := (hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs).comp (ideleClassNorm F).ker.subtype
  have hτ : Continuous (fun p : C₁ × W(-α, α, s) ↦ τ p.1 p.2) :=
    (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs).choose_spec.2.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let J := SpectralStripJetIndex χ a α s
  choose L hclosed hrep using fun ξ : PontryaginDual C₁ ↦ stripAngular_closed_radial (χ ξ) α s
  let R (ξ : PontryaginDual C₁) := (L ξ).toLinearMap.range
  choose Λ hΛ hΛg using fun j : J ↦ stripAngular_jet_normOne_dual χ hχ hα hs j
  apply stripAngular_compact_assembly κ τ hτ R hclosed _ _ (fun j : J ↦ j.val.1) Λ hΛg
    _ (Submodule.isClosed_topologicalClosure _) _ y (fun j ↦ (hΛ j y).trans (hy j))
  · rintro ξ _ ⟨f,rfl⟩ g
    change hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs g.val _ = _
    have hξ := DFunLike.congr_fun (hχ ξ) g
    exact (stripAngular_radial_eigen (χ ξ) hα hs f _ (hrep ξ f) g).trans
      (congrArg (fun z : Circle ↦ (z : ℂ) • L ξ f) hξ)
  · intro V hV hRV
    apply stripTail_angular_total χ hχ hα hs V hV
    intro ξ f z hz
    have h : L ξ f = z := Lp.ext ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq ((hrep ξ f).trans hz.symm))
    exact h ▸ hRV ξ (LinearMap.mem_range_self _ _)
  · rintro ξ z ⟨f,hf⟩ hz
    subst z
    exact hpure ξ f _ (hrep ξ f) (fun j hj ↦ (hΛ j _).symm.trans (hz j hj))

end

namespace StripDual
open scoped Classical
local notation "Wsym(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s
local notation "U(" χ ", " hα ", " hs ", " j ")" =>
  (spectralStripJet_memLp χ hα hs j).toLp (spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2)

/-- The Mellin transform of a polar-free theta test, shifted by the center of the target strip. -/
private def thetaSymbol (ψ : PontryaginDual C𝔽) (a : ℝ) (f : adelePolarSubspace F) (w : ℂ) : ℂ :=
  globalThetaMellinIntegral f.val (ideleClassNormTwist ψ ((a : ℂ) + w))

private theorem thetaSymbol_bounds (ψ : PontryaginDual C𝔽) (a : ℝ) (f : adelePolarSubspace F) :
    Differentiable ℂ (thetaSymbol ψ a f) ∧
      ∀ l r : ℝ, l ≤ r → ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc l r → ‖thetaSymbol ψ a f z‖ ≤ C :=
  stripProfile_theta_strip_bound ψ f a

/-- Multiplying an entire Schwartz–Bergman symbol by a polar-free theta transform preserves
its rapid decrease on each finite vertical strip. -/
private def thetaProduct (ψ : PontryaginDual C𝔽) (a : ℝ) (f : adelePolarSubspace F) (H : Tests) : Tests :=
  ⟨fun z ↦ thetaSymbol ψ a f z * H.val z, by
    obtain ⟨hd, hb⟩ := thetaSymbol_bounds ψ a f
    refine ⟨by simp, hd.differentiableOn.mul H.property.2.1, ?_⟩
    intro l r hlr hsub n
    obtain ⟨A, hA⟩ := hb l r hlr
    obtain ⟨B, hB⟩ := H.property.2.2 l r hlr hsub n
    refine ⟨max A 0 * max B 0, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖z ^ n * (thetaSymbol ψ a f z * H.val z)‖ ≤ _
    rw [mul_left_comm, norm_mul]
    exact mul_le_mul ((hA z hz).trans (le_max_left _ _)) ((hB ⟨z,hz,rfl⟩).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)⟩

private theorem thetaProduct_apply (ψ : PontryaginDual C𝔽) (a : ℝ) (f : adelePolarSubspace F)
    (H : Tests) (z : ℂ) : (thetaProduct ψ a f H).val z = thetaSymbol ψ a f z * H.val z := rfl

/-- The scalar test ideal generated by all polar-free theta Mellin transforms in one chart. -/
private def thetaProducts (ψ : PontryaginDual C𝔽) (a : ℝ) : Submodule ℂ Tests :=
  Submodule.span ℂ (range fun p : adelePolarSubspace F × Tests ↦ thetaProduct ψ a p.1 p.2)

private theorem thetaProduct_mem (ψ : PontryaginDual C𝔽) (a : ℝ) (f : adelePolarSubspace F) (H : Tests) :
    thetaProduct ψ a f H ∈ thetaProducts ψ a :=
  Submodule.subset_span ⟨(f,H), rfl⟩

private theorem thetaProducts_stable (ψ : PontryaginDual C𝔽) (a : ℝ) (H p : Tests) (hp : p ∈ thetaProducts ψ a) :
    timesTest H p ∈ thetaProducts ψ a := by
  have hle : thetaProducts ψ a ≤ (thetaProducts ψ a).comap (timesTest H) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨f, K⟩, rfl⟩
    change timesTest H (thetaProduct ψ a f K) ∈ thetaProducts ψ a
    have he : timesTest H (thetaProduct ψ a f K) = thetaProduct ψ a f (timesTest H K) := by
      apply Subtype.ext
      funext z
      change H.val z * (thetaSymbol ψ a f z * K.val z) = thetaSymbol ψ a f z * (H.val z * K.val z)
      ring
    exact he ▸ thetaProduct_mem ψ a f _
  exact hle hp

/-- A polynomial times the Gaussian can attain any prescribed exact vanishing order. -/
private theorem gaussian_exact_order (w : ℂ) (m : ℕ) :
    ∃ H : Tests, analyticOrderAt H.val w = (m : ℕ∞) := by
  let E (z : ℂ) := Complex.exp (z ^ 2)
  let S := schwartzBergmanSubmodule (univ : Set ℝ)
  have hE : E ∈ S := by simpa [E,S] using gaussian_mem_schwartzBergmanSubmodule univ isOpen_univ
  have hcoord {K : ℂ → ℂ} (hK : K ∈ S) : (fun z ↦ z * K z) ∈ S := by
    refine ⟨by simp, differentiableOn_id.mul hK.2.1, ?_⟩
    intro l r hlr hsub n
    obtain ⟨C, hC⟩ := hK.2.2 l r hlr hsub (n + 1)
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa only [pow_succ, mul_assoc] using hC ⟨z,hz,rfl⟩
  have hpow (n : ℕ) : (fun z ↦ (z - w) ^ n * E z) ∈ S := by
    induction n with
    | zero => simpa using hE
    | succ n ih =>
      convert S.sub_mem (hcoord ih) (S.smul_mem w ih) using 1
      funext z
      change (z - w) ^ (n+1) * E z = z * ((z-w)^n * E z) - w * ((z-w)^n * E z)
      rw [pow_succ]
      ring
  refine ⟨⟨_, hpow m⟩, ?_⟩
  change analyticOrderAt (fun z ↦ (z-w)^m * E z) w = _
  have hA : AnalyticAt ℂ E w := by dsimp only [E]; fun_prop
  have hm : analyticOrderAt (fun z : ℂ ↦ (z-w)^m) w = (m : ℕ∞) :=
    analyticOrderAt_centeredMonomial (n := m) (z₀ := w)
  rw [analyticOrderAt_fun_mul (by fun_prop) hA, hm,
    hA.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _), add_zero]

private theorem thetaSymbol_attains_order (ψ : PontryaginDual C𝔽) (a : ℝ) (w : ℂ) :
    ∃ f : adelePolarSubspace F, analyticOrderAt (thetaSymbol ψ a f) w =
      ((meromorphicOrderAt (continuedCompletedHeckeL ψ) ((a : ℂ) + w)).untop₀.toNat : ℕ∞) := by
  let u := (a : ℂ) + w
  let L := continuedCompletedHeckeL ψ
  let d := (meromorphicOrderAt L u).untop₀.toNat
  obtain ⟨hL, hspec⟩ := continuedCompletedHeckeL_spec ψ
  have hfin : meromorphicOrderAt L u ≠ ⊤ := by
    apply hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (x := 2) (mem_univ _) (mem_univ u)
    intro ht
    have hp : 0 < meromorphicOrderAt L 2 := ht ▸ WithTop.coe_lt_top (0 : ℤ)
    have hbad := completedHeckeL_continuation_zeros ψ L hL hspec (by norm_num : 0 < (2 : ℂ).re) hp
    norm_num at hbad
  have hm : max 0 (meromorphicOrderAt L u) = (d : WithTop ℤ) := by
    change max 0 (meromorphicOrderAt L u) = ((meromorphicOrderAt L u).untop₀.toNat : WithTop ℤ)
    cases ho : meromorphicOrderAt L u with
    | top => exact (hfin ho).elim
    | coe z =>
      rw [WithTop.untop₀_coe]
      change max ((0 : ℤ) : WithTop ℤ) (z : WithTop ℤ) = ((z.toNat : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_max, WithTop.coe_eq_coe]
      omega
  obtain ⟨f, hf⟩ := (isLeast_globalThetaMellinIntegral_orders ψ u).1
  refine ⟨f, ?_⟩
  let G (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist ψ z)
  have hshift : meromorphicOrderAt (thetaSymbol ψ a f) w = meromorphicOrderAt G u := by
    change meromorphicOrderAt (fun z : ℂ ↦ G ((a : ℂ) + z)) w = _
    simpa only [u, add_comm (a : ℂ) _] using
      (meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (f := G) (x := w) (c := (a : ℂ)))
  have hA := (thetaSymbol_bounds ψ a f).1.analyticAt w
  have hord : meromorphicOrderAt (thetaSymbol ψ a f) w = (d : WithTop ℤ) := hshift.trans (hf.trans hm)
  rw [hA.meromorphicOrderAt_eq] at hord
  change analyticOrderAt (thetaSymbol ψ a f) w = (d : ℕ∞)
  cases h : analyticOrderAt (thetaSymbol ψ a f) w with
  | top => simp [h] at hord
  | coe m =>
    rw [h, ENat.map_natCast] at hord
    congr 1
    exact_mod_cast (WithTop.coe_eq_coe.mp hord)

/-- An order-k derivative annihilating the theta test ideal is strictly below the
actual positive completed Hecke multiplicity at its shifted point. This includes points of
order zero and the canceled poles. -/
private theorem thetaProducts_lt_order (ψ : PontryaginDual C𝔽) (a : ℝ) (w : ℂ) (k : ℕ)
    (hvan : ∀ p ∈ thetaProducts ψ a, iteratedDeriv k p.val w = 0) :
    k < (meromorphicOrderAt (continuedCompletedHeckeL ψ) ((a : ℂ) + w)).untop₀.toNat := by
  let d := (meromorphicOrderAt (continuedCompletedHeckeL ψ) ((a : ℂ) + w)).untop₀.toNat
  by_contra! h
  obtain ⟨f, hf⟩ := thetaSymbol_attains_order ψ a w
  obtain ⟨H, hH⟩ := gaussian_exact_order w (k-d)
  let T := thetaProduct ψ a f H
  have hana : AnalyticAt ℂ H.val w :=
    (differentiableOn_univ.mp (by simpa using H.property.2.1)).analyticAt _
  have hTf : AnalyticAt ℂ (thetaSymbol ψ a f) w := (thetaSymbol_bounds ψ a f).1.analyticAt _
  have hT : AnalyticAt ℂ T.val w := hTf.mul hana
  have ht : analyticOrderAt T.val w = (k : ℕ∞) := by
    change analyticOrderAt (fun z ↦ thetaSymbol ψ a f z * H.val z) w = _
    rw [analyticOrderAt_fun_mul hTf hana, hf, hH]
    change (d : ℕ∞) + (↑(k-d) : ℕ∞) = k
    exact_mod_cast Nat.add_sub_of_le (show d ≤ k from h)
  exact (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hT).mp ht |>.2
    (hvan T (thetaProduct_mem ψ a f H))

/-- An evaluation on the dense entire-symbol chart agrees with the derivative on every
entire physical test profile represented in the scalar weighted space. -/
private theorem chart_bounded_radial_eval {α s : ℝ} (e : Tests →ₗ[ℂ] SE α s)
    (he : ∀ H, (e H : ℝ → ℂ) =ᵐ[volume] (ME.symm H).val)
    (w : ℂ) (k : ℕ) (L : StrongDual ℂ (SE α s))
    (hL : ∀ p, L (e p) = iteratedDeriv k p.val w) :
    ∀ (p : PositiveRealExponentialDecay univ) (u : SE α s), (u : ℝ → ℂ) =ᵐ[volume] p.val →
      L u = iteratedDeriv k (mellin (fun t ↦ p.val (Real.log t))) w := by
  intro p u hu
  let H : Tests := ME p
  have hrep : (e H : ℝ → ℂ) =ᵐ[volume] p.val := by
    simpa only [H, ContinuousLinearEquiv.symm_apply_apply] using he H
  have heq : u = e H := Lp.ext ((withDensity_absolutelyContinuous _ _).ae_eq (hu.trans hrep.symm))
  have hsymbol : H.val = mellin (fun t ↦ p.val (Real.log t)) := funext fun z ↦
    positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty p z (mem_univ _)
  exact (congrArg L heq).trans ((hL H).trans
    (congrArg (fun f : ℂ → ℂ ↦ iteratedDeriv k f w) hsymbol))

/-- In a single inverse-character radial component, all bounded jets that annihilate
the scalar theta ideal vanish on a vector with zero admitted arithmetic moments.
This is the scalar arithmetic hypothesis of `analytic_strip_synthesis`. -/
private theorem thetaProducts_detect_radial
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (ω : PontryaginDual C₁)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (e : Tests →ₗ[ℂ] SE α s)
    (he : ∀ H, (e H : ℝ → ℂ) =ᵐ[volume] (ME.symm H).val)
    (y : SE α s) (v : Wsym(α, s))
    (hv : (v : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * y (logNorm x))
    (hzero : ∀ j : SpectralStripJetIndex χ a α s, j.val.1 = ω →
      spectralSobolevPairing v U(χ, hα, hs, j) = 0) :
    ∀ (w : ℂ) (k : ℕ) (L : StrongDual ℂ (SE α s)),
      (∀ p, L (e p) = iteratedDeriv k p.val w) →
      (∀ p ∈ thetaProducts (χ ω) a, iteratedDeriv k p.val w = 0) → L y = 0 := by
  intro w k L hL hvan
  let n := (meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) ((a : ℂ) + w)).untop₀.toNat
  have horder : k < n := thetaProducts_lt_order (χ ω) a w k hvan
  have hb := chart_bounded_radial_eval e he w k L hL
  have hk : k < spectralStripMultiplicity α s w.re n :=
    (SharpStripEval.lt_spectralStripMultiplicity_iff_bounded_eval α s hα hs n k w).mpr ⟨horder, L, hb⟩
  have hw : ((a + w.re : ℝ) : ℂ) + (w.im : ℂ) * Complex.I = (a : ℂ) + w := by
    rw [Complex.ofReal_add, add_assoc, Complex.re_add_im]
  let j : SpectralStripJetIndex χ a α s := ⟨(ω, w.re, w.im, k), by
    change k < spectralStripMultiplicity α s w.re
      (meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) (((a + w.re : ℝ) : ℂ) + (w.im : ℂ) * Complex.I)).untop₀.toNat
    rw [hw]
    exact hk⟩
  obtain ⟨K, hK⟩ := stripTail_radial_lift (χ ω) hα hs
  have hv' : K y = v := Lp.ext ((withDensity_absolutelyContinuous _ _).ae_eq ((hK y).trans hv.symm))
  let ν := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hΛ (p : PositiveRealExponentialDecay univ) (u : SE α s) (hu : (u : ℝ → ℂ) =ᵐ[volume] p.val) :
      L u = iteratedDeriv j.val.2.2.2 (mellin (fun t ↦ p.val (Real.log t)))
        ((j.val.2.1 : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I) := by
    change L u = iteratedDeriv k _ ((w.re : ℂ) + (w.im : ℂ) * Complex.I)
    rw [Complex.re_add_im]
    exact hb p u hu
  have hp := spectralStripJet_pairing_radial_eval χ hχ ω hα hs j K hK ν
    (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽) L hΛ y
  rw [hv', hzero j rfl, ite_eq_left (show j.val.1 = ω from rfl)] at hp
  have hsc : ((Measure.haarScalarFactor μ𝔽 ν : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (by exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν).ne')
  exact (mul_eq_zero.mp hp.symm).resolve_left hsc

end StripDual

namespace StripDual
/-- Agreement of radial profiles on Lebesgue measure transports to their
inverse-character lifts for the Tamagawa measure. -/
private theorem radial_rep {α s : ℝ} (ψ : PontryaginDual C𝔽)
    (L : SE α s →L[ℂ] W(-α,α,s))
    (hL : ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (ψ x : ℂ)⁻¹ * f (logNorm x))
    (f : SE α s) (q : ℝ → ℂ) (hq : (f : ℝ → ℂ) =ᵐ[volume] q) :
    (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ ((ψ⁻¹ x : Circle) : ℂ) * q (logNorm x) := by
  let ν := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hv := (sobolev_log_preserving m𝔽 hm𝔽 hms𝔽).quasiMeasurePreserving.ae_eq_comp hq
  have ht := (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 ν).ae_eq hv
  filter_upwards [hL f,ht] with x hx hy
  rw [hx]
  change (ψ x : ℂ)⁻¹ * f (logNorm x) = (((ψ x)⁻¹ : Circle) : ℂ) * q (logNorm x)
  rw [Circle.coe_inv]
  exact congrArg ((ψ x : ℂ)⁻¹ * ·) hy

/-- The cutoffs preserve membership of every generator times every entire test
in the geometric theta space. The cutoff can be moved onto the test, after
which its inverse Mellin transform supplies the radial convolution kernel. -/
private theorem cutoff_generator_mem {α s a r : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) (hr : α+s/2 < r)
    (ψ : PontryaginDual C𝔽) (e : Tests →ₗ[ℂ] SE α s)
    (L : SE α s →L[ℂ] W(-α,α,s))
    (hL : ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (ψ x : ℂ)⁻¹ * f (logNorm x))
    (U : SE α s →L[ℂ] SE α s) (b : ℂ → ℂ)
    (hU : ∀ H : Tests, ∃ q : PositiveRealExponentialDecay (Ioo (-r) r),
      (U (e H) : ℝ → ℂ) =ᵐ[volume] q.val ∧ ∀ z, z.re ∈ Ioo (-r) r →
        mellin (fun t ↦ q.val (Real.log t)) z = b z * H.val z)
    (f : adelePolarSubspace F) (H Q : Tests)
    (hQ : ∀ z, Q.val z = globalThetaMellinIntegral f.val (ideleClassNormTwist ψ ((a:ℂ)+z)) * H.val z) :
    L (U (e Q)) ∈ globalThetaSobolev F a (neg_le_self ha) hs := by
  have h0 : 0 ∈ Ioo (-r) r := ⟨by linarith,by linarith⟩
  obtain ⟨p,-,hp⟩ := hU H
  obtain ⟨q,hq,hqM⟩ := hU Q
  apply stripTheta_generator_product_mem h0 α s a ha hs
    (show -(α+s/2) ∈ Ioo (-r) r from ⟨by linarith,by linarith⟩)
    (show α+s/2 ∈ Ioo (-r) r from ⟨by linarith,hr⟩)
    ψ f p _ q (radial_rep ψ L hL _ q.val hq)
  intro t
  have hz : ((t:ℂ)*Complex.I).re ∈ Ioo (-r) r := by simpa using h0
  rw [hqM _ hz, hp _ hz, hQ]
  ring

end StripDual

namespace StripDual
open Metric Real
private theorem choose_tail_widths (A r : ℝ) (hr : 0 < r) :
    ∃ k c : ℝ, 0 < k ∧ k < c ∧ k*(|0-A|+r) < Real.pi/2 ∧ c*r < Real.pi/2 := by
  let d := |0-A|+r
  have hd : 0 < d := add_pos_of_nonneg_of_pos (abs_nonneg _) hr
  let k := (Real.pi/2)/(d+1)
  have hk : 0 < k := by dsimp [k]; positivity
  have he : k*(d+1) = Real.pi/2 := div_mul_cancel₀ _ (by positivity)
  have hkd : k*d < Real.pi/2 := by nlinarith
  have hkr : k*r < Real.pi/2 := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (abs_nonneg _)) hk.le).trans_lt hkd
  obtain ⟨c,hc,hrc⟩ := stripReciprocal_exists_frequency k r hr.le hkr
  exact ⟨k,c,hk,hc,hkd,hrc⟩

/-- All zeros of a nonzero bounded strip generator can be exhausted by a
sequence of finite sets. The complementary products are contractive on the
smaller strip and tend pointwise to one. -/
private theorem single_generator_divisor_sequence (A k r : ℝ) (hk : 0 < k) (_hr : 0 < r)
    (hwide : k*(|0-A|+r) < Real.pi/2) (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hG₀ : G (A:ℂ) ≠ 0) (M : ℝ) (hb : ∀ z : ℂ, |z.re-A| < (Real.pi/2)/k → ‖G z‖ ≤ M) :
    let D := stripBlaschkeFromDisk (A:ℂ) k
    let B := stripBlaschkeToDisk (A:ℂ) k
    let Z := {z : ℂ // z ∈ ball 0 1 ∧ G (D z) = 0}
    let m (i : Z) := analyticOrderNatAt G (D i.val)
    let J := Ioo (-r) r
    ∃ S : ℕ → Finset Z, (∀ i : Z, 0 < m i ∧ analyticOrderAt G (D i.val) = m i) ∧
      let b (n : ℕ) (z : ℂ) := Blaschke.tail (fun i : Z ↦ i.val) m (S n) (B z)
      (∀ n, AnalyticOnNhd ℂ (b n) (Complex.re ⁻¹' J)) ∧
      (∀ n z, z.re ∈ J → ‖b n z‖ ≤ 1) ∧ (∀ z, z.re ∈ J → Tendsto (fun n ↦ b n z) atTop (𝓝 1)) := by
  intro D B Z m J
  classical
  let g := G ∘ D
  let p (i : Z) := i.val
  have hg₀ : g 0 ≠ 0 := by simpa [g,D,stripBlaschkeFromDisk] using hG₀
  have hp (i : Z) : p i ≠ 0 := by
    intro h
    have hi : g (p i) = 0 := i.property.2
    rw [h] at hi
    exact hg₀ hi
  have hpn (i : Z) : ‖p i‖ < 1 := mem_ball_zero_iff.mp i.property.1
  obtain ⟨horders, hsum⟩ := stripBlaschke_disk_zero_orders hk G
    (fun z _ ↦ hG.analyticAt z) hG₀ hb
  let : Countable Z := Set.countable_univ_iff.mp (hsum.countable_support.mono fun i _ ↦
    mul_ne_zero (Nat.cast_ne_zero.mpr ((horders i).1).ne') (sub_pos.mpr (hpn i)).ne')
  obtain ⟨S,hS⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset Z))
  refine ⟨S, fun i ↦ ⟨(horders i).1, (horders i).2.1⟩,?_⟩
  let T (n : ℕ) := Blaschke.tail p m (S n)
  have hTa (n) : AnalyticOnNhd ℂ (T n) (ball 0 1) := Blaschke.analyticOnNhd_tail p m (S n) hp hpn hsum
  have hTb (n) (z : ℂ) (hz : ‖z‖ < 1) : ‖T n z‖ ≤ 1 := Blaschke.norm_tail_le_one p m (S n) hp hpn hsum hz
  have hw (z : ℂ) (hz : z.re ∈ J) : |z.re-A| < (Real.pi/2)/k := by
    have h := abs_lt.mpr hz
    have hbound : |z.re-A| ≤ |0-A|+r := by
      rw [zero_sub,abs_neg]
      linarith [abs_sub z.re A]
    exact (lt_div_iff₀ hk).mpr (by nlinarith [mul_le_mul_of_nonneg_left hbound hk.le])
  have hB (z : ℂ) (hz : z.re ∈ J) : B z ∈ ball 0 1 := stripBlaschkeToDisk_mem hk (hw z hz)
  refine ⟨fun n z hz ↦ (hTa n _ (hB z hz)).comp (stripBlaschkeToDisk_analytic hk (hw z hz)),
    fun n z hz ↦ hTb n _ (mem_ball_zero_iff.mp (hB z hz)),fun z hz ↦ ?_⟩
  exact (Blaschke.tendsto_tail p m hp hpn hsum (mem_ball_zero_iff.mp (hB z hz))).comp hS

/-- A fixed polar-free Hecke generator supplies a strongly convergent sequence
of contractive strip symbols. Every symbol times an entire test killing the
specified finite divisor lifts into the closed theta space; all tests retain
the actual inverse Mellin formula. -/
private theorem exists_single_generator_tail_family (χ : PontryaginDual C𝔽) (a α s β r : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (hβ : 2*α+s < 2*β) (hβr : β < r)
    (e : Tests →ₗ[ℂ] SE α s) (he : ∀ H, (e H : ℝ → ℂ) =ᵐ[volume] (ME.symm H).val)
    (L : SE α s →L[ℂ] W(-α, α, s)) (hL : ∀ u, (L u : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ x : ℂ)⁻¹*u (logNorm x)) :
    ∃ (f : adelePolarSubspace F) (b : ℕ → ℂ → ℂ) (U : ℕ → SE α s →L[ℂ] SE α s)
      (S : ℕ → Finset ℂ) (m : (n : ℕ) → S n → ℕ),
      let G (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a:ℂ)+z))
      let J := Ioo (-r) r
      Differentiable ℂ G ∧ (∀ l h : ℝ, l ≤ h → ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc l h → ‖G z‖ ≤ C) ∧
      G ((2-a : ℝ) : ℂ) ≠ 0 ∧ (∀ n w, 0 < m n w) ∧ (∀ n w, analyticOrderAt G w.val = m n w) ∧
      (∀ n, AnalyticOnNhd ℂ (b n) (Complex.re ⁻¹' J)) ∧ (∀ n z, z.re ∈ J → ‖b n z‖ ≤ 1) ∧
      (∀ z, z.re ∈ J → Tendsto (fun n ↦ b n z) atTop (𝓝 1)) ∧
      (∀ y, Tendsto (fun n ↦ U n y) atTop (𝓝 y)) ∧
      (∀ n H, ∃ q : PositiveRealExponentialDecay J, (U n (e H) : ℝ → ℂ) =ᵐ[volume] q.val ∧
        ∀ z, z.re ∈ J → mellin (fun t ↦ q.val (Real.log t)) z = b n z*H.val z) ∧
      ∀ n (H : Tests), (∀ (w : S n) j, j < m n w → iteratedDeriv j H.val w.val = 0) →
        L (U n (e H)) ∈ globalThetaSobolev F a (neg_le_self hα) hs := by
  classical
  obtain ⟨f,hf⟩ := exists_stripTheta_generator_nonzero χ
  let A := 2-a
  let G (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a:ℂ)+z))
  have hG₀ : G (A:ℂ) ≠ 0 := by simpa only [G,A,Complex.ofReal_sub,Complex.ofReal_ofNat,add_sub_cancel] using hf
  obtain ⟨hG, hGB⟩ := stripProfile_theta_strip_bound χ f a
  have hr : 0 < r := by linarith
  obtain ⟨k,c,hk,hkc,hwide,hcr⟩ := choose_tail_widths A r hr
  let R := (Real.pi/2)/k
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨M,hM⟩ := hGB (A-R) (A+R) (by linarith)
  have hb0 (z : ℂ) (hz : |z.re-A| < R) : ‖G z‖ ≤ M :=
    hM z ⟨by linarith [(abs_lt.mp hz).1],by linarith [(abs_lt.mp hz).2]⟩
  let D := stripBlaschkeFromDisk (A:ℂ) k
  let B := stripBlaschkeToDisk (A:ℂ) k
  let Z := {z : ℂ // z ∈ ball 0 1 ∧ G (D z) = 0}
  let d (i : Z) := analyticOrderNatAt G (D i.val)
  obtain ⟨T,hord,hb,hcb,hpoint⟩ := single_generator_divisor_sequence A k r hk hr hwide G hG hG₀ M hb0
  let b (n : ℕ) (z : ℂ) := Blaschke.tail (fun i : Z ↦ i.val) d (T n) (B z)
  let S (n : ℕ) := (T n).image (fun i : Z ↦ D i.val)
  let m (n : ℕ) (w : S n) := analyticOrderNatAt G w.val
  have hords (n : ℕ) (w : S n) : 0 < m n w ∧ analyticOrderAt G w.val = m n w := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp w.property
    change 0 < analyticOrderNatAt G w.val ∧ analyticOrderAt G w.val = analyticOrderNatAt G w.val
    rw [← hi]
    exact hord i
  obtain ⟨U,hu,hprof⟩ := chart_tail_action hα hs hβ hβr e he atTop b (fun n ↦ (hb n).differentiableOn) hcb hpoint
  refine ⟨f,b,U,S,m,hG,hGB,hG₀,fun n w ↦ (hords n w).1,fun n w ↦ (hords n w).2,hb,hcb,hpoint,hu,hprof,?_⟩
  intro n H hkill
  have hjet (i : Z) (hi : i ∈ T n) : (d i : ℕ∞) ≤ analyticOrderAt H.val (D i.val) := by
    let w : S n := ⟨D i.val,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (test_analytic H _)).mpr (fun j hj ↦ hkill w j hj)
  obtain ⟨_,_,_,hmem⟩ := stripTheta_full_divisor_finite_jet_mem χ f α s a A k c r hα hs (by linarith)
    hk hkc hwide hcr hG₀ (T n) H hjet
  obtain ⟨q,hq,hMq⟩ := hprof n H
  exact hmem q (L (U n (e H))) hMq (radial_rep χ L hL _ q.val hq)

end StripDual

open StripDual
/-- Membership on a single inverse-character component follows from its
continuous Taylor functionals that annihilate the whole theta test ideal. -/
private theorem spectralStrip_radial_synthesis (ψ : PontryaginDual C𝔽) (a α s : ℝ)
    (ha : 0 ≤ α) (hs : 0 ≤ s) (e : Tests →ₗ[ℂ] SE α s) (he : DenseRange e)
    (her : ∀ H, (e H : ℝ → ℂ) =ᵐ[volume] (ME.symm H).val)
    (L : SE α s →L[ℂ] W(-α,α,s))
    (hL : ∀ q, (L q : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (ψ x : ℂ)⁻¹ * q (logNorm x))
    (y : SE α s) (hy : ∀ (w : ℂ) (k : ℕ) (K : StrongDual ℂ (SE α s)),
      (∀ H, K (e H) = iteratedDeriv k H.val w) →
      (∀ H ∈ thetaProducts ψ a, iteratedDeriv k H.val w = 0) → K y = 0) :
    L y ∈ Θ(a, neg_le_self ha, hs) := by
  let β := α+s+1
  let r := β+1
  have hβ : 2*α+s < 2*β := by dsimp [β]; linarith
  have hβr : β < r := by dsimp [r]; linarith
  have hr : α+s/2 < r := by linarith
  obtain ⟨f,b,U,S,m,hG,hGB,-,hm,ho,-,-,-,hlim,hprof,hideal⟩ :=
    exists_single_generator_tail_family ψ a α s β r ha hs hβ hβr e her L hL
  let G (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist ψ ((a:ℂ)+z))
  let N := (Θ(a, neg_le_self ha, hs)).comap L.toLinearMap
  have hN : IsClosed (N : Set (SE α s)) :=
    (Submodule.isClosed_topologicalClosure _).preimage L.continuous
  apply analytic_strip_synthesis N hN e he (thetaProducts ψ a) (thetaProducts_stable ψ a)
    (chart_multiplier_action ha hs hβ hβr e her) G hG hGB atTop U hlim S m hm ho hideal _ y hy
  intro n H hH
  let M := N.comap ((U n).toLinearMap.comp e)
  change H ∈ M
  have hspan : thetaProducts ψ a ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,K⟩,rfl⟩
    exact cutoff_generator_mem ha hs hr ψ e L hL (U n) (b n) (hprof n) g K _ (thetaProduct_apply ψ a g K)
  exact hspan hH

/-- Paper: Theorem 10.2.2.1, p. 446. Vanishing of every admitted moment
places a vector in the closed span of the weighted polar-free theta tests.
Deviation: At the boundary the admitted orders satisfy the strict inequality
`2k+1<s`. The proof uses Mellin division and weighted Sobolev approximation. -/
private theorem spectralStripJet_reverse_synthesis (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (y : W(-α,α,s)) (hy : ∀ j : SpectralStripJetIndex χ a α s,
      spectralSobolevPairing y ((stripU(χ, hα, hs)) j) = 0) : y ∈ Θ(a, neg_le_self hα, hs) := by
  apply spectralStripJet_reverse_of_radial_lifts χ hχ hα hs _ y hy
  intro ω p v hv hz
  obtain ⟨e, hd, he⟩ := exists_chart hα hs
  obtain ⟨L, hL⟩ := stripTail_radial_lift (χ ω) hα hs
  have hr := thetaProducts_detect_radial χ hχ ω hα hs e he p v hv hz
  have hEq : L p = v := Lp.ext ((withDensity_absolutelyContinuous _ _).ae_eq ((hL p).trans hv.symm))
  exact hEq ▸ spectralStrip_radial_synthesis (χ ω) a α s hα hs e hd he L hL p hr

end StripThetaSynthesis

/-- Paper: Theorem 10.2.2.1, p. 446. A Sobolev vector whose strip moments vanish
can be approximated in the strip norm by weighted polar-free theta tests.
Deviation: The boundary moments use the strict reciprocal-weight cutoff.
Mellin division replaces the finite-band argument on pp. 443 and 446. -/
theorem spectralStripJet_approximation (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let u : SpectralStripJetIndex χ a α s → W'(-α, α, s) := stripU(χ, hα, hs)
    let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (stripI(hα)) hs).exists.choose
    ∀ y : W(-α, α, s), (∀ j, spectralSobolevPairing y (u j) = 0) → ∀ ε > (0 : ℝ),
      ∃ f : adelePolarSubspace F, ‖y - E (Submodule.Quotient.mk f)‖ < ε := by
  intro u E y hy ε hε
  have h := spectralStripJet_reverse_synthesis χ _hχ hα hs y hy
  change y ∈ closure (E.toLinearMap.range : Set W(-α, α, s)) at h
  obtain ⟨_, ⟨q, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp h ε hε
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨f, (dist_eq_norm y (E (Submodule.Quotient.mk f))).symm.trans_lt hdist⟩

/-- Paper: Theorem 10.2.2.1, p. 446. The weighted theta closure is the common
kernel of all surviving strip evaluations.
Deviation: At the strip edges the degree satisfies `2k + 1 < s`.
The reverse inclusion uses Mellin division and approximation in the weighted strip norm. -/
theorem spectralStripJet_commonKernel (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let u : SpectralStripJetIndex χ a α s → W'(-α, α, s) := stripU(χ, hα, hs)
    JetKernel(a, stripI(hα), hs, u) := by
  intro u y
  refine ⟨spectralStripJet_commonKernel_forward χ hα hs y, fun hy ↦ ?_⟩
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (stripI(hα)) hs).exists.choose
  change y ∈ closure (E.toLinearMap.range : Set W(-α, α, s))
  refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
  obtain ⟨f, hf⟩ := spectralStripJet_approximation χ _hχ hα hs y hy ε hε
  exact ⟨_, ⟨Submodule.Quotient.mk f, rfl⟩, (dist_eq_norm _ _).trans_lt hf⟩

section

local notation "Jχ(" χ ", " a ", " α ", " s ")" => SpectralStripJetIndex χ a α s

/-- Paper: Theorem 10.2.2.1, p. 446. Common-kernel perturbations of the constructed
interpolants can be chosen so that their classes span densely in the geometric quotient.
Deviation: Finite moment support is dense by the preceding cutoff argument. The reverse
common-kernel inclusion then gives density of the single interpolants themselves. -/
private theorem spectralStripJet_interpolantDensity (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let J := Jχ(χ, a, α, s)
    let u : J → W'(-α, α, s) := stripU(χ, hα, hs)
    let v (i : J) := (spectralStripJet_singleInterpolant χ hχ hα hs i).choose
    ∃ r : J → W(-α, α, s), (∀ i j, spectralSobolevPairing (r i) (u j) = 0) ∧
      Dense (Submodule.span ℂ (range fun i ↦ (Θ(a, stripI(hα), hs)).mkQ (v i + r i)) :
        Set (spectralSobolevQuotient F a (stripI(hα)) hs)) := by
  intro J u v
  have hd := spectralStripJet_dense_quotient_of_reverse χ hχ hα hs (a := a)
    (fun x hx ↦ (spectralStripJet_commonKernel χ hχ hα hs x).mpr hx)
  refine ⟨fun _ ↦ 0, fun _ j ↦ ?_, ?_⟩
  · let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (stripI(hα)) hs).exists.choose
    let L := T.symm (u j)
    exact ((spectralSobolevPairing_dual (stripI(hα)) hs L 0).2.trans
      (congrArg (spectralSobolevPairing (0 : W(-α, α, s))) (T.apply_symm_apply (u j)))).symm.trans L.map_zero
  · simpa only [add_zero] using hd

end

/-- Paper: Theorem 10.2.2.1, p. 446. The individual strip jets admit
interpolants whose classes span densely in the geometric quotient.
Deviation: Density follows from wider-strip Blaschke products and the reverse
inclusion of the common kernel in the geometric theta closure (Theorem 10.2.2.1). -/
theorem spectralStripJet_denseInterpolants (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let J := SpectralStripJetIndex χ a α s
    let u : J → W'(-α, α, s) := stripU(χ, hα, hs)
    JetInterpolation(J, a, stripI(hα), hs, u) := by
  intro J u
  let v (i : J) := (spectralStripJet_singleInterpolant χ _hχ hα hs i).choose
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (stripI(hα)) hs).exists.choose
  let L (j : J) := T.symm (u j)
  have hL (j : J) (x : W(-α, α, s)) : L j x = spectralSobolevPairing x (u j) :=
    (spectralSobolevPairing_dual (stripI(hα)) hs (L j) x).2.trans
      (congrArg (spectralSobolevPairing x) (T.apply_symm_apply (u j)))
  let D (y : J → W(-α, α, s)) : Prop :=
    Dense (Submodule.span ℂ (range fun i ↦ (Θ(a, stripI(hα), hs)).mkQ (y i)) :
      Set (spectralSobolevQuotient F a (stripI(hα)) hs))
  have hv (i : J) : L i (v i) = 1 := (hL i _).trans (by
    simpa only [ite_true] using (spectralStripJet_singleInterpolant χ _hχ hα hs i).choose_spec i)
  have hz (i j : J) (hij : i ≠ j) : L j (v i) = 0 := (hL j _).trans (by
    simpa only [ite_eq_right (Ne.symm hij)] using
      (spectralStripJet_singleInterpolant χ _hχ hα hs i).choose_spec j)
  obtain ⟨r, hr, hd⟩ := spectralStripJet_interpolantDensity χ _hχ hα hs (a := a)
  obtain ⟨y, hy, hy', hd'⟩ := (StripInterpolation.density_iff
    (fun j ↦ (L j).toLinearMap) D v hv hz).mpr ⟨r, fun i j ↦ (hL j _).trans (hr i j), hd⟩
  exact ⟨y, fun i ↦ (hL i _).symm.trans (hy i),
    fun i j hij ↦ (hL j _).symm.trans (hy' i j hij), hd'⟩

/-- At width zero the real offset of each strip jet is zero, and its remaining
indices give exactly one line jet with the same function representative. -/
private theorem spectralLineJet_zeroWidth_indices (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (a s : ℝ) :
    ∃ e : SpectralLineJetIndex χ a s ≃ SpectralStripJetIndex χ a 0 s,
      ∀ i, stripJet(χ, e i) = lineJet(χ, i) := by
  let L := SpectralLineJetIndex χ a s
  let Z := SpectralStripJetIndex χ a 0 s
  have hoff (j : Z) : j.val.2.1 = 0 := by
    simpa using (SpectralStripJetIndex.mem_strip_order_pos (le_refl (0 : ℝ)) j).1
  have hmult (n : ℕ) : spectralStripMultiplicity 0 s 0 n = spectralBoundaryMultiplicity s n :=
    spectralStripMultiplicity_boundary le_rfl (Or.inr rfl) s n
  let e : L ≃ Z :=
    { toFun := fun i ↦ ⟨(i.val.1, 0, i.val.2.1, i.val.2.2), by
        simpa only [add_zero, hmult] using i.property⟩
      invFun := fun j ↦ ⟨(j.val.1, j.val.2.2.1, j.val.2.2.2), by
        simpa only [hoff j, add_zero, hmult] using j.property⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun j ↦ Subtype.ext (Prod.ext rfl (Prod.ext (hoff j).symm rfl)) }
  exact ⟨e, fun _ ↦ rfl⟩

/-- Transport a statement about the reindexed reciprocal-weight vectors from
the interval [−0, 0] to the identical line Sobolev space. -/
private theorem spectralLineJet_zeroWidth_transport (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (a : ℝ) {s : ℝ} (hs : 1 < s)
    (P : ∀ {l : ℝ}, l ≤ 0 → (SpectralLineJetIndex χ a s → W'(l, 0, s)) → Prop)
    (h : ∀ (e : SpectralLineJetIndex χ a s ≃ SpectralStripJetIndex χ a 0 s),
      P (stripI(le_refl (0 : ℝ))) (fun i ↦ stripU(χ, le_refl (0 : ℝ), lineHs(hs)) (e i))) :
    P (le_refl (0 : ℝ)) (lineU(χ, hs)) := by
  obtain ⟨e, he⟩ := spectralLineJet_zeroWidth_indices χ a s
  let claim (l : ℝ) (hl : l ≤ 0) := ∀ hm : ∀ i : SpectralLineJetIndex χ a s,
    MemLp (lineJet(χ, i)) 2 L2μ'(l, 0, s), P hl (fun i ↦ (hm i).toLp (lineJet(χ, i)))
  have hstrip : claim (-0) (stripI(le_refl (0 : ℝ))) := by
    intro hm
    have eqv : (fun i ↦ stripU(χ, le_refl (0 : ℝ), lineHs(hs)) (e i)) =
        fun i ↦ (hm i).toLp (lineJet(χ, i)) := by
      funext i
      exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun (he i)))
    exact eqv ▸ h e
  have transport (l : ℝ) (hl : l ≤ 0) (hl0 : l = 0) : claim l hl → claim 0 le_rfl := by
    subst l
    exact id
  exact transport (-0) _ neg_zero hstrip (spectralLineJet_memLp χ hs)

section LineThetaSynthesis

open scoped SchwartzMap ContDiff Interval

/-- On Haar-integrable representatives, the zero-line Schwartz action is exactly
multiplication of Fourier transforms on every component. -/
private theorem lineProfile_fourier_action {s : ℝ} (hs : 0 ≤ s) (φ : SchwartzBruhat C𝔽)
    (u : CompactIntervalSobolev μ𝔽 logNorm 0 0 s) (hu : Integrable (u : C𝔽 → ℂ) μ𝔽) :
    let A := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose
    Integrable (A φ u : C𝔽 → ℂ) μ𝔽 ∧
      lcaFourier μ𝔽 (A φ u) = lcaFourier μ𝔽 φ * lcaFourier μ𝔽 u := by
  intro A
  let w := (μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))
  have hle : μ𝔽 ≤ w := by
    calc
      μ𝔽 = (μ𝔽).withDensity 1 := withDensity_one.symm
      _ ≤ _ := withDensity_mono (.of_forall fun g ↦ by
        change 1 ≤ ENNReal.ofReal (intervalSobolevDensity 0 0 s _)
        rw [ENNReal.one_le_ofReal]
        simpa [intervalSobolevDensity] using Real.one_le_rpow
          (le_add_of_nonneg_right (sq_nonneg _)) (by linarith : 0 ≤ s / 2))
  obtain ⟨J, hJ⟩ := exists_L2_restriction w μ𝔽 hle
  have hφ := ((schwartzBruhat_fourier_equiv μ𝔽).choose_spec φ).1
  have hAe : (A φ u : C𝔽 → ℂ) =ᵐ[μ𝔽] lcaConvolution μ𝔽 φ u := (hJ _).symm.trans
    (pettis_convolution_haar_L2 μ𝔽 J hJ (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs)
      (hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s le_rfl hs)
      (exists_hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).choose_spec.2 φ hφ u (A φ u)
      ((existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose_spec φ u))
  refine ⟨(lcaConvolution_integrable μ𝔽 hφ hu).2.1.congr hAe.symm, ?_⟩
  refine Eq.trans (b := lcaFourier μ𝔽 (lcaConvolution μ𝔽 φ u)) ?_ (lcaFourier_convolution μ𝔽 hφ hu)
  funext ψ
  exact integral_congr_ae (hAe.mul Filter.EventuallyEq.rfl)

local notation "WI(" s ")" => CompactIntervalSobolev μ𝔽 logNorm 0 0 s
local notation "Wχ(" χ ", " s ", " hs ")" =>
  actionIsotype ((hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).comp (ideleClassNorm F).ker.subtype) ((χ).comp restriction)

private theorem lineProfile_sobolevLift (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽)
    (hP : ∀ p (k : C₁) x, P p (k.val⁻¹*x) = (χ k.val : ℂ) * P p x) :
    ∃ e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs), ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ) := by
  let w := (μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))
  have hle : μ𝔽 ≤ w := by
    calc
      μ𝔽 = (μ𝔽).withDensity 1 := withDensity_one.symm
      _ ≤ _ := withDensity_mono (.of_forall fun g ↦ by
        change 1 ≤ ENNReal.ofReal (intervalSobolevDensity 0 0 s _)
        rw [ENNReal.one_le_ofReal]
        simpa [intervalSobolevDensity] using Real.one_le_rpow
          (le_add_of_nonneg_right (sq_nonneg _)) (by linarith : 0 ≤ s / 2))
  have hv (u : SchwartzBruhat C𝔽) : MemLp (u : C𝔽 → ℂ) 2 w := by
    have hmw : w = sobolevMeasure μ𝔽 (modulatedSobolevWeight m𝔽) s := intervalSobolev_zero_eq_sobolevMeasure m𝔽 μ𝔽 s
    exact (congrArg (fun v : Measure C𝔽 ↦ MemLp (u : C𝔽 → ℂ) 2 v) hmw).mpr (SchwartzBruhat.memLp_modulatedSobolev μ𝔽 m𝔽 u s hs)
  let j : SchwartzBruhat C𝔽 →ₗ[ℂ] WI(s) := {
    toFun := fun u ↦ (hv u).toLp u
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  have hj (u : SchwartzBruhat C𝔽) : (j u : C𝔽 → ℂ) =ᵐ[μ𝔽] (u : C𝔽 → ℂ) :=
    hle.absolutelyContinuous.ae_eq (hv u).coeFn_toLp
  have hmem (p : 𝓢(ℝ, ℂ)) : j (P p) ∈ Wχ(χ, s, hs) := by
    apply (mem_actionIsotype _ _ _).mpr
    intro k
    apply Lp.ext
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
    have htr := (measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving.ae_eq_comp (hj (P p))
    have hsm := hle.absolutelyContinuous.ae_eq (Lp.coeFn_smul (χ k.val : ℂ) (j (P p)))
    filter_upwards [hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s le_rfl hs k.val (j (P p)), htr, hsm, hj (P p)] with x h₁ h₂ h₃ h₄
    exact h₁.trans (h₂.trans ((hP p k x).trans ((congrArg ((χ k.val : ℂ) * ·) h₄.symm).trans h₃.symm)))
  let e := (j.comp P.toLinearMap).codRestrict Wχ(χ, s, hs) hmem
  exact ⟨e,fun p ↦ hj (P p)⟩

local notation "EXω(" χ ")" => actionIsotype
  (((exists_modulatedExponentialDecay_translationAction (G := C𝔽) m𝔽 univ hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose).comp (ideleClassNorm F).ker.subtype)
  ((χ).comp restriction)
private theorem lineProfile_decay_as_schwartz (χ : PontryaginDual C𝔽) (f : EXω(χ)) :
    ∃ v : SchwartzBruhat C𝔽, (v : C𝔽 → ℂ) = f.val.val ∧
      ∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (χ k.val : ℂ) * v x := by
  have hW : f.val.val ∈ schwartzBruhatSubmodule C𝔽 := by
    simpa only [modulationWeight_zero] using
      modulationWeight_mem_schwartzBruhat m𝔽 univ ⟨0, mem_univ _⟩ f.val
  let v : SchwartzBruhat C𝔽 := ⟨f.val.val,hW⟩
  have hρ := (exists_modulatedExponentialDecay_translationAction (G := C𝔽) m𝔽 univ
    hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose_spec
  have hiso (k : C₁) (x : C𝔽) : v (k.val⁻¹*x) = (χ k.val : ℂ) * v x :=
    (hρ.1 k.val f.val x).symm.trans (congrArg (fun u : ModulatedExponentialDecay m𝔽 univ ↦ u.val x)
      ((mem_actionIsotype _ _ _).mp f.property k))
  exact ⟨v, rfl, hiso⟩

private theorem lineProfile_denseTestMap (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s) :
    ∃ i : EXω(χ) →L[ℂ] Wχ(χ, s, hs), DenseRange i ∧ ∀ f, ((i f).val : C𝔽 → ℂ) =ᵐ[μ𝔽] f.val.val := by
  let i := (existsUnique_spectralLineTestCompletion (F := F) 0 hs (χ.comp restriction)).exists.choose
  have hi := (existsUnique_spectralLineTestCompletion (F := F) 0 hs (χ.comp restriction)).exists.choose_spec
  exact ⟨i, hi.2.1, fun f ↦ (hi.1 f).trans (.of_forall fun g ↦ congrFun (modulationWeight_zero m𝔽 f.val.val) g)⟩

/-- The distribution-free chart is dense directly in the weighted norm. The
surjectivity on homogeneous Schwartz tests includes the norm-dense concentrated
exponential tests of §10.2.1. -/
private theorem lineProfile_denseEmbedding (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽)
    (honto : ∀ v : SchwartzBruhat C𝔽, (∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (χ k.val : ℂ) * v x) → ∃ p, P p = v)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs)) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ)) :
    DenseRange e := by
  let H := lineProfile_denseTestMap (F := F) χ s hs
  let i := H.choose
  have hi := H.choose_spec.2
  have hr (f : EXω(χ)) : i f ∈ range e := by
    let v := (lineProfile_decay_as_schwartz (F := F) χ f).choose
    have hv := (lineProfile_decay_as_schwartz (F := F) χ f).choose_spec
    let p := (honto v hv.2).choose
    have hp : P p = v := (honto v hv.2).choose_spec
    have hrep' : ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] f.val.val := (hrep p).trans
      (.of_forall fun g ↦ (congrArg (fun z : SchwartzBruhat C𝔽 ↦ z g) hp).trans (congrFun hv.1 g))
    exact ⟨p, Subtype.ext (Lp.ext ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq (hrep'.trans (hi f).symm)))⟩
  exact H.choose_spec.1.mono (Set.range_subset_iff.mpr hr)

private theorem lineProfile_eq_of_fourier {s : ℝ} (u v : WI(s)) (hu : Integrable (u : C𝔽 → ℂ) μ𝔽)
    (hv : Integrable (v : C𝔽 → ℂ) μ𝔽) (h : ∀ ψ, lcaFourier μ𝔽 u ψ = lcaFourier μ𝔽 v ψ) : u = v := by
  let H := lcaFourier_L1 μ𝔽
  let f : Lp ℂ 1 μ𝔽 := hu.toL1 u
  let g : Lp ℂ 1 μ𝔽 := hv.toL1 v
  have hf : (f : C𝔽 → ℂ) =ᵐ[μ𝔽] (u : C𝔽 → ℂ) := hu.coeFn_toL1
  have hg : (g : C𝔽 → ℂ) =ᵐ[μ𝔽] (v : C𝔽 → ℂ) := hv.coeFn_toL1
  have hfg : H.choose f = H.choose g := by
    apply ZeroAtInftyContinuousMap.ext
    intro ψ
    rw [H.choose_spec.1 f ψ, H.choose_spec.1 g ψ]
    exact (integral_congr_ae (hf.mul EventuallyEq.rfl)).trans
      ((h ψ).trans (integral_congr_ae (hg.symm.mul EventuallyEq.rfl)))
  have hfg' : f = g := H.choose_spec.2.1 hfg
  have hrep : (f : C𝔽 → ℂ) =ᵐ[μ𝔽] (g : C𝔽 → ℂ) := by rw [hfg']
  exact Lp.ext ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq (hf.symm.trans (hrep.trans hg)))

private theorem lineProfile_action_of_symbols {s : ℝ} (hs : 0 ≤ s) (φ : SchwartzBruhat C𝔽)
    (u v : WI(s)) (hu : Integrable (u : C𝔽 → ℂ) μ𝔽) (hv : Integrable (v : C𝔽 → ℂ) μ𝔽)
    (heq : ∀ ψ, lcaFourier μ𝔽 φ ψ * lcaFourier μ𝔽 u ψ = lcaFourier μ𝔽 v ψ) :
    (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose φ u = v := by
  have h := lineProfile_fourier_action (F := F) (s := s) hs φ u hu
  exact lineProfile_eq_of_fourier (F := F) (s := s) _ v h.1 hv (fun ψ ↦ (congrFun h.2 ψ).trans (heq ψ))

/-- Multiplication by an arbitrary real Schwartz profile in the frequency chart
equals the ambient zero-line action of its inverse Fourier kernel. -/
private theorem lineProfile_chart_intertwine (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (hoff : ∀ p ψ, ψ ∉ range γ → lcaFourier μ𝔽 (P p) ψ = 0)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs)) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (h p : 𝓢(ℝ, ℂ)) :
    let A := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose
    A (P h) (e p).val = (e (SchwartzMap.smulLeftCLM ℂ (h : ℝ → ℂ) p)).val := by
  intro A
  have hi (p : 𝓢(ℝ, ℂ)) : Integrable ((e p).val : C𝔽 → ℂ) μ𝔽 := (SchwartzBruhat.integrable μ𝔽 (P p)).congr (hrep p).symm
  have hhat (p : 𝓢(ℝ, ℂ)) (ψ) : lcaFourier μ𝔽 (e p).val ψ = lcaFourier μ𝔽 (P p) ψ :=
    integral_congr_ae ((hrep p).mul EventuallyEq.rfl)
  let q := SchwartzMap.smulLeftCLM ℂ (h : ℝ → ℂ) p
  apply lineProfile_action_of_symbols (F := F) (s := s) hs (P h) (e p).val (e q).val (hi p) (hi q)
  intro ψ
  refine (congrArg (lcaFourier μ𝔽 (P h) ψ * ·) (hhat p ψ)).trans (Eq.trans ?_ (hhat q ψ).symm)
  by_cases hψ : ψ ∈ range γ
  · obtain ⟨t,rfl⟩ := hψ
    exact (congrArg₂ (· * ·) (hF h t) (hF p t)).trans
      (((SchwartzMap.smulLeftCLM_apply_apply h.hasTemperateGrowth p t).symm).trans (hF q t).symm)
  · rw [hoff h ψ hψ, zero_mul, hoff q ψ hψ]

private theorem lineProfile_chart_multiplier (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs))
    (hint : ∀ h p : 𝓢(ℝ, ℂ), (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose (P h) (e p).val =
      (e (SchwartzMap.smulLeftCLM ℂ (h : ℝ → ℂ) p)).val) (h : 𝓢(ℝ, ℂ)) :
    ∃ T : Wχ(χ, s, hs) →L[ℂ] Wχ(χ, s, hs), ∀ p,
      T (e p) = e (SchwartzMap.smulLeftCLM ℂ (h : ℝ → ℂ) p) := by
  let A := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose
  let E := Wχ(χ, s, hs)
  let τ := hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs
  have hmem (v : E) : A (P h) v.val ∈ E := by
    apply (mem_actionIsotype _ _ _).mpr
    intro k
    exact spectral_integrated_action_eigenvector μ𝔽 τ (P h : C𝔽 → ℂ) v.val _
      ((existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose_spec _ _) k.val (χ k.val : ℂ)
      ((mem_actionIsotype _ _ _).mp v.property k)
  exact ⟨((A (P h)).comp E.subtypeL).codRestrict E hmem, fun p ↦ Subtype.ext (hint h p)⟩

private theorem lineProfile_compact_of_frequencyBand (χ : PontryaginDual C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x)) (p : 𝓢(ℝ, ℂ))
    (φ : SchwartzBruhat C𝔽) (n : ℕ) (hF : ∀ t, lcaFourier μ𝔽 φ (γ t) = p t)
    (hband : tsupport (lcaFourier μ𝔽 φ) ⊆ modulatedFrequencyBand m𝔽 χ⁻¹ (-(n:ℝ)) n) :
    HasCompactSupport (p : ℝ → ℂ) := by
  obtain ⟨u, hu⟩ := exists_modulatedFrequencyLine m𝔽 hm𝔽 hms𝔽
  have hcurve (t : ℝ) : γ t = χ⁻¹ * (u (Multiplicative.ofAdd (-t))).val :=
    PontryaginDual.ext fun x ↦ (hγ t x).trans (congrArg ((χ x)⁻¹ * ·) (hu (-t) x).symm)
  have hcov : support (p : ℝ → ℂ) ⊆ Icc (-(n:ℝ)) n := by
    intro t ht
    have hh : γ t ∈ support (lcaFourier μ𝔽 φ) := by change lcaFourier μ𝔽 φ (γ t) ≠ 0; rwa [hF t]
    have hb := hband (subset_tsupport _ hh)
    obtain ⟨v, hv, hvψ⟩ := hb
    have heq : χ⁻¹ * (u (Multiplicative.ofAdd v)).val = γ t :=
      PontryaginDual.ext fun x ↦ (congrArg ((χ x)⁻¹ * ·) (hu v x)).trans (hvψ x).symm
    rw [hcurve] at heq
    have ht' : v = -t := congrArg Multiplicative.toAdd (u.injective (Subtype.ext (mul_left_cancel heq)))
    constructor <;> linarith [hv.1,hv.2]
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hcov isClosed_Icc)

/-- The Chapter 10 isotype approximate identity has genuine compactly supported
ordinary Schwartz symbols in the normalized chart, and converges strongly in the
Sobolev norm of that isotype. -/
private theorem lineProfile_chart_approximateUnit (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (honto : ∀ v : SchwartzBruhat C𝔽, (∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (χ k.val : ℂ) * v x) → ∃ p, P p = v)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs))
    (hint : ∀ h p : 𝓢(ℝ, ℂ), (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose (P h) (e p).val =
      (e (SchwartzMap.smulLeftCLM ℂ (h : ℝ → ℂ) p)).val) :
    ∃ (g : ℕ → 𝓢(ℝ, ℂ)) (T : ℕ → Wχ(χ, s, hs) →L[ℂ] Wχ(χ, s, hs)),
      (∀ n, HasCompactSupport (g n : ℝ → ℂ)) ∧ (∀ n p, T n (e p) = e (SchwartzMap.smulLeftCLM ℂ (g n : ℝ → ℂ) p)) ∧
      ∀ y, Tendsto (fun n ↦ T n y) atTop (𝓝 y) := by
  let H := exists_spectralLineIsotypeConvolution (F := F) χ hs
  let φ := H.choose
  let T := H.choose_spec.choose
  have hu := H.choose_spec.choose_spec
  let g (n : ℕ) := (honto (φ n) (hu.2.1 n)).choose
  have hg (n : ℕ) : P (g n) = φ n := (honto (φ n) (hu.2.1 n)).choose_spec
  refine ⟨g,T,fun n ↦ ?_, fun n p ↦ ?_, hu.2.2.2.2⟩
  · exact lineProfile_compact_of_frequencyBand (F := F) χ γ hγ (g n) (φ n) n
      (fun t ↦ (congrArg (fun f : SchwartzBruhat C𝔽 ↦ lcaFourier μ𝔽 f (γ t)) (hg n).symm).trans (hF (g n) t)) (hu.2.2.1 n)
  · apply Subtype.ext
    exact (hu.2.2.2.1 n (e p)).trans (((congrArg (fun f : SchwartzBruhat C𝔽 ↦
      (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose f (e p).val) (hg n).symm)).trans (hint (g n) p))

private theorem lineProfile_pettis_mem_closed {X V : Type*}
    [Group X] [MeasurableSpace X] (μ : Measure X) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (K : Submodule ℂ V) (hK : IsClosed (K : Set V))
    (τ : X →* (V →L[ℂ] V)) (hτ : ∀ g, ∀ v ∈ K, τ g v ∈ K) {ψ : X → ℂ} {u b : V}
    (hu : u ∈ K) (hb : HasPettisIntegral (.positive μ) (fun g ↦ ψ g • τ g u) b) : b ∈ K := by
  have : CompleteSpace K := hK.completeSpace_coe
  rw [← K.orthogonal_orthogonal]
  intro w hw
  have hδ := congrArg
    (fun z : PettisWeakCompletion V ↦ (show Module.Dual ℂ (StrongDual ℂ V) from z)
      (innerSL ℂ w)) hb.2
  change innerSL ℂ w b = ∫ g, innerSL ℂ w (ψ g • τ g u) ∂μ at hδ
  rw [innerSL_apply_apply] at hδ
  rw [hδ]
  refine integral_eq_zero_of_ae (.of_forall fun g ↦ ?_)
  change innerSL ℂ w (ψ g • τ g u) = 0
  rw [innerSL_apply_apply]
  exact (K.mem_orthogonal' w).mp hw _ (K.smul_mem _ (hτ g u hu))

/-- All Schwartz convolutions on the zero-width line preserve the closed weighted
theta image, including the inverse transforms of arbitrary smooth compact frequency profiles. -/
private theorem lineProfile_preserves_theta (a : ℝ) {s : ℝ} (hs : 0 ≤ s) (φ : SchwartzBruhat C𝔽) :
    let K := globalThetaSobolev F a (le_rfl : (0 : ℝ) ≤ 0) hs
    let A := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose
    ∀ v ∈ K, A φ v ∈ K := by
  intro K A v hv
  let τ := hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs
  obtain ⟨ρ, hρ, -, -⟩ := exists_globalThetaSobolevAction (F := F) a (le_rfl : (0 : ℝ) ≤ 0) hs
  have hτ (g : C𝔽) : ∀ v ∈ K, τ g v ∈ K := fun v hv ↦
    (hρ g ⟨v,hv⟩) ▸ (ρ g ⟨v,hv⟩).property
  exact lineProfile_pettis_mem_closed μ𝔽 K (Submodule.isClosed_topologicalClosure _) τ hτ hv
    ((existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose_spec φ v)

/-- On the normalized line the ordinary Fourier transform of the centered theta
representative is its global theta Mellin transform, evaluated at the shifted center. -/
private theorem lineProfile_weightedTheta (χ : PontryaginDual C𝔽) (a : ℝ)
    (γ : ℝ → PontryaginDual C𝔽) (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (f : adelePolarSubspace F) :
    Integrable (modulationWeight m𝔽 a (adelicTheta f.val)) μ𝔽 ∧ ∀ t,
      lcaFourier μ𝔽 (modulationWeight m𝔽 a (adelicTheta f.val)) (γ t) =
      globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a, t))) := by
  obtain ⟨hf,hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hw (g : C𝔽) :
      adelicTheta f.val g * (ideleClassNormTwist (1 : PontryaginDual C𝔽) (a : ℂ)) g =
      modulationWeight m𝔽 a (adelicTheta f.val) g := by
    have hp : 0 < ((m𝔽 g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    change _ * ((1 : ℂ) * (((m𝔽 g).val : ℝ) : ℂ) ^ (a : ℂ)) = ((((m𝔽 g).val : ℝ) ^ a : ℝ) : ℂ) * _
    rw [one_mul, ← Complex.ofReal_cpow hp.le]
    exact mul_comm _ _
  refine ⟨(globalThetaMellinIntegral_integrable_of_vanishing f.val hf hf' _).congr (.of_forall hw), fun t ↦ ?_⟩
  apply integral_congr_ae
  refine .of_forall fun g ↦ ?_
  have hp : 0 < ((m𝔽 g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hψ : γ t g = (χ g * Circle.exp (t * logNorm g))⁻¹ := by
    rw [hγ, neg_mul, Circle.exp_neg, mul_inv]
  have hph : star (γ t g : ℂ) = (χ g : ℂ) * Complex.exp (((t * logNorm g : ℝ) : ℂ) * Complex.I) := by
    rw [hψ, Circle.coe_inv_eq_conj, ← Complex.star_def, star_star, Circle.coe_mul, Circle.coe_exp]
  change modulationWeight m𝔽 a (adelicTheta f.val) g * star (γ t g : ℂ) = _
  rw [hph]
  change (((((m𝔽 g).val : ℝ) ^ a : ℝ) : ℂ) * adelicTheta f.val g) * _ =
    adelicTheta f.val g * ((χ g : ℂ) * ((((m𝔽 g).val : ℝ) : ℂ) ^ (shift(a, t))))
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le,
    Real.rpow_def_of_pos hp, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_mul,
    mul_add, Complex.exp_add]
  rw [show (t : ℂ) * (logNorm g : ℂ) * Complex.I = (logNorm g : ℂ) * ((t : ℂ) * Complex.I) by ring]
  ring_nf
  rfl

/-- A Schwartz profile given by a multiplier times an adelic polar-free Mellin
transform belongs to the closed global theta space in the weighted isotype. -/
private theorem lineProfile_theta_generator (χ : PontryaginDual C𝔽) (a s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (hoff : ∀ p ψ, ψ ∉ range γ → lcaFourier μ𝔽 (P p) ψ = 0)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs)) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (f : adelePolarSubspace F) (h p : 𝓢(ℝ, ℂ))
    (hp : ∀ t, p t = h t * globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a, t)))) :
    (e p).val ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs := by
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 s le_rfl hs).exists.choose
  let u := E (Submodule.Quotient.mk f)
  have hu := (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 s le_rfl hs).exists.choose_spec.2 f
  have hm := lineProfile_weightedTheta χ a γ hγ f
  have hi : Integrable (u : C𝔽 → ℂ) μ𝔽 := hm.1.congr hu.symm
  have hv := (SchwartzBruhat.integrable μ𝔽 (P p)).congr (hrep p).symm
  have huF (t) : lcaFourier μ𝔽 u (γ t) = globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a, t))) :=
    (integral_congr_ae (hu.mul EventuallyEq.rfl)).trans (hm.2 t)
  have hEq : (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs).exists.choose (P h) u = (e p).val := by
    apply lineProfile_action_of_symbols (F := F) (s := s) hs (P h) u (e p).val hi hv
    intro ψ
    refine Eq.trans (b := lcaFourier μ𝔽 (P p) ψ) ?_ (integral_congr_ae ((hrep p).symm.mul EventuallyEq.rfl))
    by_cases hψ : ψ ∈ range γ
    · obtain ⟨t,rfl⟩ := hψ
      rw [hF, huF, hF, hp t]
    · rw [hoff h ψ hψ, zero_mul, hoff p ψ hψ]
  rw [← hEq]
  exact lineProfile_preserves_theta (F := F) a hs (P h) u
    (Submodule.le_topologicalClosure _ (LinearMap.mem_range_self E.toLinearMap _))

/-- The finite span of smooth symbols multiplied by compact Schwartz cutoffs
maps into a submodule once its individual Schwartz generators do. -/
private theorem lineProfile_theta_compact_ideal {E I : Type*} [AddCommMonoid E] [Module ℂ E]
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] E) (N : Submodule ℂ E) (Z : I → ℝ → ℂ)
    (hZ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Z i))
    (hgen : ∀ (i : I) (h p : 𝓢(ℝ, ℂ)), (∀ t, p t = h t * Z i t) → e p ∈ N)
    (p : 𝓢(ℝ, ℂ)) (hspan : (p : ℝ → ℂ) ∈ Submodule.span ℂ {v : ℝ → ℂ |
      ∃ (i : I) (h : 𝓢(ℝ, ℂ)), HasCompactSupport (h : ℝ → ℂ) ∧ ∀ t, v t = h t * Z i t}) :
    e p ∈ N := by
  let C : 𝓢(ℝ, ℂ) →ₗ[ℂ] (ℝ → ℂ) := { toFun := fun h ↦ h, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have hle : Submodule.span ℂ {v : ℝ → ℂ | ∃ (i : I) (h : 𝓢(ℝ, ℂ)),
      HasCompactSupport (h : ℝ → ℂ) ∧ ∀ t, v t = h t * Z i t} ≤ (N.comap e).map C := by
    apply Submodule.span_le.mpr
    rintro v ⟨i,h,hc,hv⟩
    have heq : v = (h : ℝ → ℂ) * Z i := funext hv
    have hvc : HasCompactSupport v := heq ▸ hc.mul_right
    have hvd : ContDiff ℝ (⊤ : ℕ∞) v := heq ▸ (h.smooth _).mul (hZ i)
    let q := hvc.toSchwartzMap hvd
    exact ⟨q, hgen i h q hv, rfl⟩
  obtain ⟨q,hq,heq⟩ := hle hspan
  exact (show q = p from DFunLike.ext q p (congrFun heq)) ▸ hq

/-- A smooth one-variable function whose first `m` Taylor coefficients vanish is
smoothly divisible by the corresponding power of the coordinate, including at the point. -/
private theorem lineProfile_smooth_divide {f : ℝ → ℂ} (hf : ContDiff ℝ (∞) f)
    (a : ℝ) (m : ℕ) (hj : ∀ k < m, iteratedDeriv k f a = 0) :
    ∃ q : ℝ → ℂ, ContDiff ℝ (∞) q ∧ ∀ x, f x = ((x - a) ^ m : ℝ) • q x := by
  cases m with
  | zero => exact ⟨f, hf, fun x ↦ by simp⟩
  | succ n =>
    let D := iteratedDeriv (n+1) f
    let Z (x u : ℝ) := ((1-u)^n / n.factorial : ℝ) • D ((x-a)*u+a)
    let q (x : ℝ) := ∫ u in Ioc (0 : ℝ) 1, Z x u
    have hD : ContDiff ℝ (∞) D := by
      simpa only [D, iteratedDeriv_eq_iterate] using ContDiff.iterate_deriv (n+1) hf
    have hq : ContDiff ℝ (∞) q := by
      apply ContDiff.parametric_integral (μ := volume) (f := Z) isCompact_Icc (Ioc_subset_Icc_self) (by simp)
      change ContDiff ℝ (∞) (fun v : ℝ × ℝ ↦ ((1-v.2)^n / n.factorial : ℝ) • D ((v.1-a)*v.2+a))
      exact (by fun_prop : ContDiff ℝ (∞) (fun v : ℝ × ℝ ↦ (1-v.2)^n / (n.factorial : ℝ))).smul (hD.comp (by fun_prop))
    refine ⟨q, hq, fun x ↦ ?_⟩
    rcases eq_or_ne a x with rfl | hax
    · simpa using hj 0 (by omega)
    have hu : UniqueDiffOn ℝ (uIcc a x) := uniqueDiffOn_uIcc hax
    have hder (k : ℕ) (z : ℝ) (hz : z ∈ uIcc a x) : iteratedDerivWithin k f (uIcc a x) z = iteratedDeriv k f z :=
      iteratedDerivWithin_eq_iteratedDeriv hu ((hf.of_le (by simp)).contDiffAt) hz
    have hzero : taylorWithinEval f n (uIcc a x) a x = 0 := by
      rw [taylor_within_apply]
      apply Finset.sum_eq_zero
      intro k hk
      rw [hder _ _ left_mem_uIcc, hj k (Finset.mem_range.mp hk), smul_zero]
    let H (t : ℝ) := ((x-t)^n / n.factorial : ℝ) • D t
    have hF : f x = ∫ t in a..x, H t := by
      have h := taylor_integral_remainder (x := x) (x₀ := a) (n := n) ((hf.of_le (by simp)).contDiffOn)
      rw [hzero, sub_zero] at h
      refine h.trans (intervalIntegral.integral_congr fun t ht ↦ ?_)
      rw [hder _ _ ht]
    have hchange := intervalIntegral.smul_integral_comp_mul_add (a := (0:ℝ)) (b := 1) H (x-a) a
    have hh (u : ℝ) : H ((x-a)*u+a) = (x-a)^n • Z x u := by
      simp only [H, Z, smul_smul]
      rw [show x-((x-a)*u+a) = (x-a)*(1-u) by ring, mul_pow]
      congr 1
      ring
    rw [show q x = ∫ u in (0:ℝ)..1, Z x u from (intervalIntegral.integral_of_le (by norm_num)).symm]
    calc
      f x = ∫ t in a..x, H t := hF
      _ = (x-a) • ∫ u in (0:ℝ)..1, H ((x-a)*u+a) := by simpa only [zero_mul, one_mul, mul_zero, mul_one, zero_add, sub_add_cancel] using hchange.symm
      _ = (x-a) • (x-a)^n • ∫ u in (0:ℝ)..1, Z x u := by simp_rw [hh, intervalIntegral.integral_smul]
      _ = (x-a)^(n+1) • ∫ u in (0:ℝ)..1, Z x u := by rw [smul_smul, pow_succ']

/-- A frequency cutoff supported on a patch where a symbol has the prescribed
zero order turns local smooth division into a compactly supported multiplier. -/
private theorem lineProfile_compact_divide {p b e G : ℝ → ℂ} (hp : ContDiff ℝ (∞) p)
    (hb : ContDiff ℝ (∞) b) (hc : HasCompactSupport b) (a : ℝ) (m : ℕ)
    (hj : ∀ k < m, iteratedDeriv k p a = 0) (hone : ∀ x, p x ≠ 0 → b x = 1)
    (hunit : ∀ x ∈ tsupport b, ContDiffAt ℝ (∞) e x ∧ e x ≠ 0 ∧ G x = ((x-a)^m : ℝ) • e x) :
    ∃ h : ℝ → ℂ, ContDiff ℝ (∞) h ∧ HasCompactSupport h ∧ ∀ x, p x = h x * G x := by
  obtain ⟨q, hq, hdiv⟩ := lineProfile_smooth_divide hp a m hj
  let h := fun x ↦ b x * (q x / e x)
  have hh : ContDiff ℝ (∞) h := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport b
    · simpa only [h, div_eq_mul_inv] using hb.contDiffAt.mul (hq.contDiffAt.mul ((hunit x hx).1.fun_inv (hunit x hx).2.1))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      exact (notMem_tsupport_iff_eventuallyEq.mp hx).mono fun y hy ↦ by simp [h, hy]
  refine ⟨h, hh, hc.mul_right, fun x ↦ ?_⟩
  have hp' : p x = b x * p x := by
    by_cases hx : p x = 0
    · simp [hx]
    · rw [hone x hx, one_mul]
  by_cases hx : x ∈ tsupport b
  · rw [hp', hdiv x, (hunit x hx).2.2]
    dsimp only [h]
    simp only [Complex.real_smul]
    field_simp [(hunit x hx).2.1]
  · rw [hp', show h x = 0 by simp [h, image_eq_zero_of_notMem_tsupport hx],
      image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

/-- On a vertical frequency line an exact complex analytic order gives a smooth
nonvanishing local unit times the corresponding power of the real coordinate. -/
private theorem lineProfile_analyticFactor {Z : ℂ → ℂ} (a t₀ : ℝ) (m : ℕ)
    (hZ : AnalyticAt ℂ Z ((a : ℂ) + (t₀ : ℂ) * Complex.I))
    (hord : meromorphicOrderAt Z ((a : ℂ) + (t₀ : ℂ) * Complex.I) = (m : WithTop ℤ)) :
    ∃ (U : Set ℝ) (e : ℝ → ℂ), IsOpen U ∧ t₀ ∈ U ∧ ∀ t ∈ U,
      ContDiffAt ℝ (∞) e t ∧ e t ≠ 0 ∧ Z ((a : ℂ) + (t : ℂ) * Complex.I) = ((t - t₀) ^ m : ℝ) • e t := by
  let A (t : ℝ) : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  have hA : ContDiff ℝ (∞) A := contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hz : analyticOrderAt Z (A t₀) = (m : ℕ∞) := by
    rw [hZ.meromorphicOrderAt_eq] at hord
    cases h : analyticOrderAt Z (A t₀) with
    | top => change (analyticOrderAt Z (A t₀)).map (fun n : ℕ ↦ (n : ℤ)) = _ at hord; simp [h] at hord
    | coe r =>
      change (analyticOrderAt Z (A t₀)).map (fun n : ℕ ↦ (n : ℤ)) = _ at hord
      rw [h, ENat.map_natCast] at hord
      congr 1
      exact_mod_cast (WithTop.coe_eq_coe.mp hord)
  obtain ⟨g, hg, hg₀, heq⟩ := hZ.analyticOrderAt_eq_natCast.mp hz
  let e (t : ℝ) := Complex.I ^ m * g (A t)
  have hall : ∀ᶠ z in 𝓝 (A t₀), AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ Z z = (z - A t₀) ^ m • g z :=
    hg.eventually_analyticAt.and (hg.continuousAt.eventually_ne hg₀ |>.and heq)
  have hnear := hA.continuous.continuousAt.preimage_mem_nhds hall
  obtain ⟨U, hsub, hopen, ht₀⟩ := mem_nhds_iff.mp hnear
  refine ⟨U, e, hopen, ht₀, fun t ht ↦ ?_⟩
  obtain ⟨hg, hne, hform⟩ := hsub ht
  refine ⟨contDiffAt_const.mul ((hg.restrictScalars (𝕜 := ℝ)).contDiffAt.comp t hA.contDiffAt),
    mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) hne, ?_⟩
  rw [hform]
  simp only [e, A, smul_eq_mul, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_sub]
  rw [show (a : ℂ) + t * Complex.I - (a + t₀ * Complex.I) = (t - t₀) * Complex.I by ring, mul_pow, mul_assoc]

/-- Every fixed real frequency has a neighborhood and a single polar-free theta test
generating all smooth profiles there with vanishing Taylor jet through the local Hecke order.
The multiplier is a compactly supported Schwartz function on the whole frequency line. -/
private theorem lineProfile_theta_compact_patch (χ : PontryaginDual C𝔽) (a t₀ : ℝ) :
    let m := (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(a, t₀))).untop₀.toNat
    ∃ (f : adelePolarSubspace F) (r : ℝ), 0 < r ∧ ∀ (p : ℝ → ℂ), ContDiff ℝ (∞) p →
      tsupport p ⊆ Metric.ball t₀ r → (∀ k < m, iteratedDeriv k p t₀ = 0) →
      ∃ h : 𝓢(ℝ, ℂ), HasCompactSupport (h : ℝ → ℂ) ∧ ∀ t,
        p t = h t * globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a, t))) := by
  intro m
  let L := continuedCompletedHeckeL χ
  let w : ℂ := shift(a, t₀)
  obtain ⟨hL, hLval⟩ := continuedCompletedHeckeL_spec χ
  have hfinite : meromorphicOrderAt L w ≠ ⊤ := by
    apply hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (x := 2) (mem_univ _) (mem_univ w)
    intro htop
    have hp : 0 < meromorphicOrderAt L 2 := htop ▸ WithTop.coe_lt_top (0 : ℤ)
    have hbad := completedHeckeL_continuation_zeros χ L hL hLval (by norm_num : 0 < (2 : ℂ).re) hp
    norm_num at hbad
  have hm : max 0 (meromorphicOrderAt L w) = (m : WithTop ℤ) := by
    change max 0 (meromorphicOrderAt L w) = ((meromorphicOrderAt L w).untop₀.toNat : WithTop ℤ)
    cases ho : meromorphicOrderAt L w with
    | top => exact (hfinite ho).elim
    | coe z =>
      rw [WithTop.untop₀_coe]
      change max ((0 : ℤ) : WithTop ℤ) (z : WithTop ℤ) = ((z.toNat : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_max, WithTop.coe_eq_coe]
      omega
  obtain ⟨f, hf⟩ := (isLeast_globalThetaMellinIntegral_orders χ w).1
  obtain ⟨hf₀, hf₁⟩ := (mem_adelePolarSubspace f.val).mp f.property
  let Z := fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist χ z)
  have han : AnalyticAt ℂ Z w :=
    (globalThetaMellinIntegral_entire_of_vanishing f.val hf₀ hf₁ χ).analyticAt w
  obtain ⟨U, e, hU, ht₀, hu⟩ := lineProfile_analyticFactor a t₀ m han (hf.trans hm)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ht₀)
  let B : ContDiffBump t₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let b := fun t ↦ ((B t : ℝ) : ℂ)
  have hbs : tsupport b ⊆ U := by
    refine (tsupport_comp_subset Complex.ofReal_zero B).trans ?_
    rw [B.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by change r / 2 < r; linarith)).trans hsub
  refine ⟨f, r / 4, by positivity, fun p hp hs hj ↦ ?_⟩
  have hone (t : ℝ) (ht : p t ≠ 0) : b t = 1 := by
    have ht' : t ∈ Metric.closedBall t₀ B.rIn :=
      Metric.ball_subset_closedBall (hs (subset_tsupport _ (mem_support.mpr ht)))
    simp [b, B.one_of_mem_closedBall ht']
  obtain ⟨h, hh, hc, heq⟩ := lineProfile_compact_divide (G := fun t ↦ Z (shift(a, t)))
    hp (Complex.ofRealCLM.contDiff.comp B.contDiff) (B.hasCompactSupport.comp_left Complex.ofReal_zero)
    t₀ m hj hone (fun t ht ↦ hu t (hbs ht))
  exact ⟨hc.toSchwartzMap hh, hc, heq⟩

/-- On an entire frequency component, any compactly supported smooth profile which
vanishes to full Hecke order at every zero is a finite linear combination of exact
theta profiles times compactly supported Schwartz multipliers. -/
private theorem lineProfile_theta_compact_span (χ : PontryaginDual C𝔽) (a : ℝ)
    (p : ℝ → ℂ) (hp : ContDiff ℝ (∞) p) (hc : HasCompactSupport p)
    (hj : ∀ (t : ℝ) (k : ℕ), k < (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(a, t))).untop₀.toNat →
      iteratedDeriv k p t = 0) :
    p ∈ Submodule.span ℂ {v : ℝ → ℂ | ∃ (f : adelePolarSubspace F) (h : 𝓢(ℝ, ℂ)),
      HasCompactSupport (h : ℝ → ℂ) ∧ ∀ t, v t = h t *
        globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a, t)))} := by
  classical
  let S := Submodule.span ℂ {v : ℝ → ℂ | ∃ (f : adelePolarSubspace F) (h : 𝓢(ℝ, ℂ)),
    HasCompactSupport (h : ℝ → ℂ) ∧ ∀ t, v t = h t *
      globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a, t)))}
  choose f r hr hpatch using fun t : ℝ ↦ lineProfile_theta_compact_patch χ a t
  have hlocal (i : ℝ) (q : ℝ → ℂ) (hq : ContDiff ℝ (∞) q) (hsub : tsupport q ⊆ Metric.ball i (r i)) :
      q * p ∈ S := by
    have hqp (k : ℕ) (hk : k < (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(a, i))).untop₀.toNat) :
        iteratedDeriv k (q * p) i = 0 := by
      rw [iteratedDeriv_mul (hq.of_le (by simp)).contDiffAt (hp.of_le (by simp)).contDiffAt]
      apply Finset.sum_eq_zero
      intro j _
      rw [hj i (k - j) ((Nat.sub_le _ _).trans_lt hk), mul_zero]
    obtain ⟨h, hh, heq⟩ := hpatch i (q * p) (hq.mul hp) (tsupport_mul_subset_left.trans hsub) hqp
    exact Submodule.subset_span ⟨f i, h, hh, heq⟩
  let B (i : ℝ) : ContDiffBump i := ⟨r i / 4, r i / 2, by have := hr i; positivity, by linarith [hr i]⟩
  let b (i t : ℝ) := ((B i t : ℝ) : ℂ)
  have hb (i : ℝ) : ContDiff ℝ (∞) (b i) := Complex.ofRealCLM.contDiff.comp (B i).contDiff
  have hbs (i : ℝ) : tsupport (b i) ⊆ Metric.ball i (r i) := by
    refine (tsupport_comp_subset Complex.ofReal_zero (B i)).trans ?_
    rw [(B i).tsupport_eq]
    exact Metric.closedBall_subset_ball (by change r i / 2 < r i; linarith [hr i])
  have hcov : tsupport p ⊆ ⋃ i : ℝ, Metric.ball i (r i / 4) :=
    fun x _ ↦ mem_iUnion.mpr ⟨x, Metric.mem_ball_self (by have := hr x; positivity)⟩
  obtain ⟨K, hK⟩ := hc.elim_finite_subcover (fun i : ℝ ↦ Metric.ball i (r i / 4))
    (fun _ ↦ Metric.isOpen_ball) hcov
  let Q (J : Finset ℝ) (t : ℝ) := ∏ i ∈ J, (1 - b i t)
  have hQins (J : Finset ℝ) (i : ℝ) (hi : i ∉ J) : Q (insert i J) = (1 - b i) * Q J := by
    funext t
    simp [Q, hi]
  have hQempty : Q ∅ = 1 := by funext t; simp [Q]
  have hQ (J : Finset ℝ) : ContDiff ℝ (∞) (Q J) := by
    induction J using Finset.induction_on with
    | empty => rw [hQempty]; exact contDiff_const
    | @insert i J hi ih => rw [hQins J i hi]; exact (contDiff_const.sub (hb i)).mul ih
  have hpart (J : Finset ℝ) : p - Q J * p ∈ S := by
    induction J using Finset.induction_on with
    | empty => simp [hQempty]
    | @insert i J hi ih =>
      rw [hQins J i hi, show p - ((1 - b i) * Q J) * p =
        (p - Q J * p) + (b i * Q J) * p by ring]
      exact S.add_mem ih (hlocal i (b i * Q J) ((hb i).mul (hQ J)) (tsupport_mul_subset_left.trans (hbs i)))
  have hzero : Q K * p = 0 := by
    funext t
    by_cases ht : p t = 0
    · simp [ht]
    · obtain ⟨i, hi, ht'⟩ := mem_iUnion₂.mp (hK (subset_tsupport _ (mem_support.mpr ht)))
      have hb1 : b i t = 1 := by
        have ht'' : t ∈ Metric.closedBall i (B i).rIn := Metric.ball_subset_closedBall ht'
        simp [b, (B i).one_of_mem_closedBall ht'']
      have hQt : Q K t = 0 := Finset.prod_eq_zero hi (by rw [hb1, sub_self])
      simp [hQt]
  change p ∈ S
  simpa only [hzero, sub_zero] using hpart K

/-- Every compact Schwartz profile with full Hecke zero multiplicities in its
Taylor jet gives a genuine element of the closed global weighted theta image. -/
private theorem lineProfile_hecke_compactIdeal (χ : PontryaginDual C𝔽) (a s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (hoff : ∀ p ψ, ψ ∉ range γ → lcaFourier μ𝔽 (P p) ψ = 0)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs)) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (p : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (p : ℝ → ℂ))
    (hj : ∀ (t : ℝ) (k : ℕ), k < (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(a,t))).untop₀.toNat →
      iteratedDeriv k p t = 0) :
    (e p).val ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs := by
  let Z (f : adelePolarSubspace F) (t : ℝ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ (shift(a,t)))
  have hd (f : adelePolarSubspace F) : ContDiff ℝ (⊤ : ℕ∞) (Z f) := by
    obtain ⟨hf,hf'⟩ := (mem_adelePolarSubspace f.val).mp f.property
    have hE := globalThetaMellinIntegral_entire_of_vanishing f.val hf hf' χ
    exact (hE.contDiff.restrict_scalars ℝ).comp (contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const))
  exact lineProfile_theta_compact_ideal ((Wχ(χ, s, hs)).subtype.comp e) _ Z hd
    (lineProfile_theta_generator χ a s hs P γ hγ hF hoff e hrep) p (lineProfile_theta_compact_span χ a p (p.smooth _) hc hj)

/-- Positive Hecke jet orders on a vertical frequency chart are locally finite. -/
private theorem continuedCompletedHeckeL_finite_vertical_zeros_on_compact (χ : PontryaginDual C𝔽) (a : ℝ) (K : Set ℝ) (hK : IsCompact K) :
    {t ∈ K | 0 < (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(a, t))).untop₀.toNat}.Finite := by
  let A (t : ℝ) := shift(a, t)
  let L := continuedCompletedHeckeL χ
  have hA : Continuous A := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hi : Injective A := fun x y h ↦ by simpa [A, Complex.add_im, Complex.mul_im] using congrArg Complex.im h
  have hL : MeromorphicOn L (A '' K) := fun z _ ↦ (continuedCompletedHeckeL_spec χ).1.meromorphicOn z (mem_univ z)
  have hf := (MeromorphicOn.divisor L (A '' K)).finiteSupport (hK.image hA)
  apply (hf.preimage hi.injOn).subset
  rintro t ⟨ht, hpos⟩
  change MeromorphicOn.divisor L (A '' K) (A t) ≠ 0
  rw [hL.divisor_apply ⟨t, ht, rfl⟩]
  change 0 < (meromorphicOrderAt L (A t)).untop₀.toNat at hpos
  exact fun heq ↦ by rw [heq] at hpos; simp at hpos

/-- The frequency derivative of a Fourier integral is a log moment. Only
polynomial moments up to the requested order enter this real-variable formula. -/
private theorem iteratedDeriv_oscillatory_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (L : X → ℝ) (hL : Measurable L) (f : X → ℂ) (k : ℕ)
    (hi : ∀ j ≤ k, Integrable (fun x ↦ f x * (L x : ℂ) ^ j) μ) (t : ℝ) :
    iteratedDeriv k (fun u : ℝ ↦ ∫ x, f x * Complex.exp (((u * L x : ℝ) : ℂ) * Complex.I) ∂μ) t =
      Complex.I ^ k * ∫ x, f x * (L x : ℂ) ^ k * Complex.exp (((t * L x : ℝ) : ℂ) * Complex.I) ∂μ := by
  let A (j : ℕ) (u : ℝ) (x : X) :=
    (f x * (L x : ℂ) ^ j) * Complex.I ^ j * Complex.exp (((u * L x : ℝ) : ℂ) * Complex.I)
  have hnorm (j u x) : ‖A j u x‖ = ‖f x * (L x : ℂ) ^ j‖ := by
    simp only [A, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one,
      Complex.norm_exp_ofReal_mul_I]
  have hmeas (j) (hj : j ≤ k) (u : ℝ) : AEStronglyMeasurable (A j u) μ := by
    refine ((hi j hj).aestronglyMeasurable.mul_const _).mul ?_
    exact (Complex.continuous_exp.measurable.comp
      ((Complex.continuous_ofReal.measurable.comp (hL.const_mul u)).mul_const _)).aestronglyMeasurable
  have hint (j) (hj : j ≤ k) (u : ℝ) : Integrable (A j u) μ :=
    (hi j hj).norm.mono' (hmeas j hj u) (.of_forall fun x ↦ (hnorm j u x).le)
  have hder (j) (hj : j+1 ≤ k) (u : ℝ) :
      HasDerivAt (fun v ↦ ∫ x, A j v x ∂μ) (∫ x, A (j+1) u x ∂μ) u := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ) univ_mem
      (.of_forall (hmeas j (by omega))) (hint j (by omega) u) (hmeas _ hj u)
      (.of_forall fun x v _ ↦ (hnorm (j+1) v x).le) (hi _ hj).norm ?_).2
    refine .of_forall fun x v _ ↦ ?_
    have hd := (((hasDerivAt_id v).mul_const (L x)).ofReal_comp.mul_const Complex.I).cexp
    convert hd.const_mul ((f x * (L x : ℂ)^j) * Complex.I^j) using 1
    · simp [A]
    · simp [A, pow_succ]
      ring
  have hall (j) (hj : j ≤ k) :
      iteratedDeriv j (fun u : ℝ ↦ ∫ x, f x * Complex.exp (((u * L x : ℝ) : ℂ) * Complex.I) ∂μ) =
        fun u ↦ ∫ x, A j u x ∂μ := by
    induction j with
    | zero => simp [A]
    | succ j ih =>
      rw [iteratedDeriv_succ, ih (by omega)]
      exact funext fun u ↦ (hder j hj u).deriv
  rw [hall k le_rfl, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun x ↦ by dsimp [A]; ring)

local notation "Hscalar(" s ")" => CompactIntervalSobolev volume id 0 0 s
local notation "nuF" => canonicalModulatedHaar m𝔽 hm𝔽
local notation "rad(" χ ", " u ")" => (fun x : C𝔽 ↦ ((χ⁻¹ x : Circle) : ℂ) * u (logNorm x))

local instance lineProfile_canonicalHaar : (nuF : Measure C𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1

private theorem lineProfile_radial_homogeneous (χ : PontryaginDual C𝔽) (u : ℝ → ℂ)
    (k : C₁) (x : C𝔽) : rad(χ, u) (k.val⁻¹*x) = (χ k.val : ℂ) * rad(χ, u) x := by
  have hm : m𝔽 (k.val⁻¹*x) = m𝔽 x := by
    rw [map_mul, map_inv, show m𝔽 k.val = 1 from k.property, inv_one, one_mul]
  change (((χ (k.val⁻¹*x))⁻¹ : Circle) : ℂ) * u (Real.log ((m𝔽 (k.val⁻¹*x)).val : ℝ)) =
    (χ k.val : ℂ) * ((((χ x)⁻¹ : Circle) : ℂ) * u (logNorm x))
  rw [hm, map_mul, map_inv, mul_inv_rev, inv_inv, Circle.coe_mul]
  ring_nf
  rfl

/-- Pullback by the log norm times the inverse character defines a bounded
map of the scalar singleton Sobolev space into the Tamagawa-weighted isotype. -/
private theorem lineProfile_weighted_radial (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s) :
    ∃ L : Hscalar(s) →L[ℂ] Wχ(χ, s, hs), ∀ u,
      ((L u).val : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, (u : ℝ → ℂ)) := by
  let ν := nuF
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let E := globalThetaAmbient_equiv_canonical (F := F) hm𝔽 0 0 s
  let B := E.choose
  let R := exists_modulatedIntervalSobolev_characterLogPullback m𝔽 hm𝔽 hms𝔽 χ⁻¹ 0 0 s
  let T : Hscalar(s) →L[ℂ] WI(s) := B.symm.toContinuousLinearMap.comp R.choose
  have ht (u : Hscalar(s)) : (T u : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, (u : ℝ → ℂ)) := by
    have hE := (E.choose_spec (T u)).1.symm
    have hB : B (T u) = R.choose u := B.apply_symm_apply _
    have hb : (B (T u) : C𝔽 → ℂ) =ᵐ[μ𝔽] (R.choose u : C𝔽 → ℂ) :=
      .of_forall fun g ↦ congrArg (fun v : ModulatedIntervalSobolev m𝔽 hm𝔽 0 0 s ↦ v g) hB
    exact hE.trans (hb.trans
      ((Measure.absolutelyContinuous_isHaarMeasure μ𝔽 ν).ae_eq (R.choose_spec.1 u)))
  have hac : μ𝔽 ≪ (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm x))) :=
    withDensity_absolutelyContinuous' (((continuous_intervalSobolevDensity' 0 0 s).measurable.comp
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).measurable.log).ennreal_ofReal.aemeasurable)
      (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (intervalSobolevDensity_pos 0 0 s _)).ne')
  have hmem (u : Hscalar(s)) : T u ∈ Wχ(χ, s, hs) := by
    apply (mem_actionIsotype _ _ _).mpr
    intro k
    apply Lp.ext
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
    have htr := (measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving.ae_eq_comp (ht u)
    have hsm := hac.ae_eq (Lp.coeFn_smul (χ k.val : ℂ) (T u))
    filter_upwards [hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s le_rfl hs k.val (T u), htr, hsm, ht u] with x h₁ h₂ h₃ h₄
    exact h₁.trans (h₂.trans ((lineProfile_radial_homogeneous χ u k x).trans ((congrArg ((χ k.val : ℂ) * ·) h₄.symm).trans h₃.symm)))
  exact ⟨T.codRestrict _ hmem,ht⟩

private theorem lineProfile_scalar_has_schwartz (χ : PontryaginDual C𝔽) (f : PositiveRealExponentialDecay univ) :
    ∃ ψ : SchwartzBruhat C𝔽, ∀ x, ψ x = rad(χ, f.val) x := by
  exact (exists_modulatedIntervalSobolev_characterLogPullback m𝔽 hm𝔽 hms𝔽 χ⁻¹ 0 0 0).choose_spec.2 f

/-- Canonical logarithmic Haar coordinates give the Fourier transform of
a character-twisted scalar profile with the exact Tamagawa normalization. -/
private theorem lineProfile_scalar_fourier (χ : PontryaginDual C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (f : PositiveRealExponentialDecay univ) (t : ℝ) :
    lcaFourier μ𝔽 rad(χ, f.val) (γ t) =
      ((Measure.haarScalarFactor μ𝔽 nuF : ℝ) : ℂ) *
        mellin (fun x ↦ f.val (Real.log x)) ((t : ℂ) * Complex.I) := by
  let ν := nuF
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hfun (x : C𝔽) : rad(χ, f.val) x * star (γ t x : ℂ) =
      f.val (logNorm x) * Complex.exp (((t:ℂ)*Complex.I) * (logNorm x : ℂ)) := by
    have hψ : γ t x = (χ x * Circle.exp (t * logNorm x))⁻¹ := by rw [hγ,neg_mul,Circle.exp_neg,mul_inv]
    have hph : star (γ t x : ℂ) = (χ x : ℂ) * Complex.exp (((t * logNorm x : ℝ) : ℂ)*Complex.I) := by
      rw [hψ,Circle.coe_inv_eq_conj, ← Complex.star_def,star_star,Circle.coe_mul,Circle.coe_exp]
    change (((χ x)⁻¹ : Circle) : ℂ) * f.val (logNorm x) * star (γ t x : ℂ) = _
    rw [hph,Circle.coe_inv,Complex.ofReal_mul,show (t:ℂ)*(logNorm x : ℂ)*Complex.I = (t:ℂ)*Complex.I*(logNorm x : ℂ) by ring]
    field_simp [Circle.coe_ne_zero]
  have hprofile := (integral_congr_ae (.of_forall hfun) : lcaFourier μ𝔽 rad(χ, f.val) (γ t) = _)
  refine hprofile.trans ?_
  rw [mellin_logProfile]
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν,integral_smul_nnreal_measure]
  rw [NNReal.smul_def, Complex.real_smul]
  congr 1
  have hl := sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have hc : Continuous f.val := by
    refine (logExponentialDecayTwist univ ⟨0,mem_univ _⟩ f).continuous.congr ?_
    intro x
    simpa using logExponentialDecayTwist_apply univ ⟨0,mem_univ _⟩ f x
  let q (x : ℝ) := f.val x * Complex.exp (((t:ℂ)*Complex.I)*(x:ℂ))
  have hq : Continuous q := hc.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  exact (integral_map hl.measurable.aemeasurable (f := q) hq.aestronglyMeasurable).symm.trans
    (congrArg (fun η : Measure ℝ ↦ ∫ x, q x ∂η) hl.map_eq)

/-- Restriction of an entire Mellin transform to the imaginary axis multiplies
its kth complex derivative by the kth power of the frequency phase. -/
private theorem lineProfile_vertical_scalar_derivative (f : PositiveRealExponentialDecay univ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun v : ℝ ↦ mellin (fun x ↦ f.val (Real.log x)) ((v : ℂ)*Complex.I)) t =
      Complex.I^k * iteratedDeriv k (mellin (fun x ↦ f.val (Real.log x))) ((t : ℂ)*Complex.I) := by
  let Z := positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty f
  have hZ : Z.val = mellin (fun x ↦ f.val (Real.log x)) :=
    funext fun w ↦ positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty f w (mem_univ _)
  have hd : Differentiable ℂ Z.val := by simpa only [preimage_univ,differentiableOn_univ] using Z.property.2.1
  have hall (n : ℕ) : iteratedDeriv n (fun v : ℝ ↦ Z.val ((v : ℂ)*Complex.I)) =
      fun v : ℝ ↦ Complex.I^n * iteratedDeriv n Z.val ((v:ℂ)*Complex.I) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ,ih]
      funext v
      have hD := (hd.contDiff.differentiable_iteratedDeriv' n ((v : ℂ)*Complex.I)).hasDerivAt
      have hC := (hD.comp (v : ℂ) ((hasDerivAt_id (v : ℂ)).mul_const Complex.I)).comp_ofReal
      have hh := (hC.const_mul (Complex.I^n)).deriv
      change deriv (fun x : ℝ ↦ Complex.I^n * iteratedDeriv n Z.val ((x:ℂ)*Complex.I)) v = _
      refine hh.trans ?_
      rw [iteratedDeriv_succ,pow_succ]
      simp only [one_mul]
      ring
  rw [← hZ]
  exact congrFun (hall k) t

private theorem lineProfile_scalar_chart_test (χ : PontryaginDual C𝔽)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (honto : ∀ v : SchwartzBruhat C𝔽, (∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (χ k.val : ℂ) * v x) → ∃ p, P p = v)
    (f : PositiveRealExponentialDecay univ) :
    ∃ p : 𝓢(ℝ, ℂ), (∀ x, P p x = rad(χ, f.val) x) ∧ ∀ t, p t = ((Measure.haarScalarFactor μ𝔽 nuF : ℝ) : ℂ) *
        mellin (fun x ↦ f.val (Real.log x)) ((t : ℂ) * Complex.I) := by
  obtain ⟨v,hv⟩ := lineProfile_scalar_has_schwartz (F := F) χ f
  have huv (k : C₁) (x : C𝔽) : v (k.val⁻¹*x) = (χ k.val : ℂ) * v x :=
    (hv _).trans ((lineProfile_radial_homogeneous χ f.val k x).trans (congrArg ((χ k.val : ℂ) * ·) (hv x).symm))
  obtain ⟨p,hp⟩ := honto v huv
  have heq (x : C𝔽) : P p x = rad(χ, f.val) x := (congrArg (fun u : SchwartzBruhat C𝔽 ↦ u x) hp).trans (hv x)
  refine ⟨p, heq, fun t ↦ (hF p t).symm.trans ?_⟩
  exact (congrArg (fun v : C𝔽 → ℂ ↦ lcaFourier μ𝔽 v (γ t)) (funext heq)).trans (lineProfile_scalar_fourier χ γ hγ f t)

private theorem lineProfile_scalar_test_in_chart (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s)
    (L : Hscalar(s) →L[ℂ] Wχ(χ, s, hs)) (hL : ∀ u, ((L u).val : C𝔽 → ℂ) =ᵐ[μ𝔽] rad(χ, (u : ℝ → ℂ)))
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs)) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (f : PositiveRealExponentialDecay univ) (u : Hscalar(s)) (hu : (u : ℝ → ℂ) =ᵐ[volume] f.val)
    (p : 𝓢(ℝ, ℂ)) (hp : ∀ x, P p x = rad(χ, f.val) x) :
    L u = e p := by
  have h := (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 nuF).ae_eq
    ((sobolev_log_preserving m𝔽 hm𝔽 hms𝔽).quasiMeasurePreserving.ae_eq_comp hu)
  apply Subtype.ext
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
  filter_upwards [hL u, h, hrep p] with x hx hx' hx''
  exact hx.trans ((congrArg (fun z : ℂ ↦ (χ⁻¹ x : ℂ)*z) hx').trans ((hp x).symm.trans hx''.symm))

private theorem lineProfile_scalar_endpoint_criterion (s : ℝ) (hs : 0 ≤ s) (c : ℂ) (hc : c ≠ 0)
    (t : ℝ) (k : ℕ) (Λ : Hscalar(s) →L[ℂ] ℂ)
    (h : ∀ (f : PositiveRealExponentialDecay univ) (u : Hscalar(s)), (u : ℝ → ℂ) =ᵐ[volume] f.val →
      Λ u = (c*Complex.I^k) * iteratedDeriv k (mellin (fun x ↦ f.val (Real.log x))) ((t : ℂ)*Complex.I)) :
    2 * (k : ℝ) + 1 < s := by
  apply (scalarIntervalSobolev_eval_boundary_iff 0 0 s le_rfl hs k ((t : ℂ)*Complex.I) (by simp)).mp
  refine ⟨(c*Complex.I^k)⁻¹ • Λ,fun f u hu ↦ ?_⟩
  change (c * Complex.I^k)⁻¹ * Λ u = _
  rw [h f u hu, inv_mul_cancel_left₀ (mul_ne_zero hc (pow_ne_zero k Complex.I_ne_zero))]

private theorem lineProfile_scalar_test_derivative (c : ℂ) (t : ℝ) (k : ℕ) (p : 𝓢(ℝ, ℂ)) (f : PositiveRealExponentialDecay univ)
    (hp : ∀ v, p v = c*mellin (fun x ↦ f.val (Real.log x)) ((v : ℂ) * Complex.I)) :
    iteratedDeriv k p t = (c*Complex.I^k)*iteratedDeriv k (mellin (fun x ↦ f.val (Real.log x))) ((t : ℂ)*Complex.I) := by
  have hpf : (p : ℝ → ℂ) = fun v : ℝ ↦ c * mellin (fun x ↦ f.val (Real.log x)) ((v : ℂ)*Complex.I) := funext hp
  rw [hpf,iteratedDeriv_const_mul_field,lineProfile_vertical_scalar_derivative,mul_assoc]

/-- An individual chart derivative extends to this isotype only in the exact
strict range prescribed by the scalar endpoint Sobolev theorem. -/
private theorem lineProfile_jet_endpoint_necessary (χ : PontryaginDual C𝔽) (s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (honto : ∀ v : SchwartzBruhat C𝔽, (∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (χ k.val : ℂ) * v x) → ∃ p, P p = v)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ, s, hs)) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (t : ℝ) (k : ℕ) (Λ : StrongDual ℂ Wχ(χ, s, hs)) (hΛ : ∀ p, Λ (e p) = iteratedDeriv k p t) :
    2 * (k : ℝ) + 1 < s := by
  let H := lineProfile_weighted_radial (F := F) χ s hs
  let B := H.choose
  let c : ℂ := ((Measure.haarScalarFactor μ𝔽 nuF : ℝ) : ℂ)
  have hpos : 0 < (Measure.haarScalarFactor μ𝔽 nuF : ℝ) := by exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 nuF
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  apply lineProfile_scalar_endpoint_criterion s hs c hc t k (Λ.comp B)
  intro f u hu
  let Htest := lineProfile_scalar_chart_test χ P γ hγ hF honto f
  let p := Htest.choose
  have heq := lineProfile_scalar_test_in_chart χ s hs B H.choose_spec P e hrep f u hu p Htest.choose_spec.1
  exact (congrArg Λ heq).trans ((hΛ p).trans (lineProfile_scalar_test_derivative c t k p f Htest.choose_spec.2))

private theorem lineJet_as_phase (η : PontryaginDual C𝔽) (t : ℝ) (n : ℕ) (g : C𝔽) :
    spectralZeroJet η 0 t n g =
      ((η g : ℂ) * Complex.exp (((t * logNorm g : ℝ) : ℂ) * Complex.I)) * (logNorm g : ℂ)^n := by
  have hp : (0 : ℝ) < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change ((η g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ ((0 : ℂ) + (t : ℂ) * Complex.I)) * _ = _
  rw [zero_add, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le, Complex.ofReal_mul]
  ring_nf

/-- The real-frequency Fourier profile of a Sobolev vector differentiates at every
surviving order. With the conjugation used by the Fourier transform, its chart
runs through the inverses of the Mellin characters. -/
private theorem spectralLineJet_fourier_profile_derivative
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s)
    (j : SpectralLineJetIndex χ a s) (f : WI(s)) (Ψ : ℝ → PontryaginDual C𝔽)
    (hΨ : ∀ u g, star ((Ψ u) g : ℂ) = (χ j.val.1 g : ℂ) *
      Complex.exp (((u * logNorm g : ℝ) : ℂ) * Complex.I)) :
    iteratedDeriv j.val.2.2 (fun u ↦ lcaFourier μ𝔽 f (Ψ u)) j.val.2.1 =
      Complex.I ^ j.val.2.2 * spectralSobolevPairing f ((spectralLineJet_memLp χ hs j).toLp
        (spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2)) := by
  have hL : Measurable logNorm := (NNReal.continuous_coe.comp (Units.continuous_val.comp
    (isProperMap_ideleClassNorm F).continuous)).measurable.log
  have hi (n) (hn : n ≤ j.val.2.2) :
      Integrable (fun x ↦ (f x * (χ j.val.1 x : ℂ)) * (logNorm x : ℂ)^n) μ𝔽 := by
    let i : SpectralLineJetIndex χ a s := ⟨(j.val.1, j.val.2.1, n), hn.trans_lt j.property⟩
    have h := ((spectralLineJet_functional χ hs i).choose_spec.1 f).1
    refine h.norm.mono' ((((Lp.stronglyMeasurable f).measurable.mul
      (continuous_subtype_val.comp (χ j.val.1).continuous).measurable).mul
      ((Complex.measurable_ofReal.comp hL).pow_const n)).aestronglyMeasurable) (.of_forall fun x ↦ ?_)
    change _ ≤ ‖f x * spectralZeroJet (χ j.val.1) 0 j.val.2.1 n x‖
    rw [lineJet_as_phase]
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, mul_assoc, le_refl]
  have hp := iteratedDeriv_oscillatory_integral μ𝔽 logNorm hL _ _ hi j.val.2.1
  have hF (u : ℝ) : lcaFourier μ𝔽 f (Ψ u) = ∫ x, (f x * (χ j.val.1 x : ℂ)) *
      Complex.exp (((u * logNorm x : ℝ) : ℂ) * Complex.I) ∂μ𝔽 :=
    integral_congr_ae (.of_forall fun x ↦ (congrArg (f x * ·) (hΨ u x)).trans (mul_assoc _ _ _).symm)
  rw [show (fun u ↦ lcaFourier μ𝔽 f (Ψ u)) = _ from funext hF, hp]
  congr 1
  let z := spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
  let v := (spectralLineJet_memLp χ hs j).toLp z
  have hac : μ𝔽 ≪ (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm x))⁻¹) :=
    withDensity_absolutelyContinuous'
      (((continuous_intervalSobolevDensity' 0 0 s).measurable.comp hL).inv.ennreal_ofReal.aemeasurable)
      (.of_forall fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (intervalSobolevDensity_pos 0 0 s _)))
  have hv : (v : C𝔽 → ℂ) =ᵐ[μ𝔽] z := hac.ae_eq (MemLp.coeFn_toLp _)
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  change _ = f x * v x
  rw [hx, show z x = _ from lineJet_as_phase _ _ _ x]
  ring

private theorem lineJet_chart_star {ψ χ : PontryaginDual C𝔽} {t : ℝ}
    (hp : ∀ g, ψ g = (χ g)⁻¹ * Circle.exp (-t * logNorm g)) (x : C𝔽) :
    star (ψ x : ℂ) = (χ x : ℂ) * Complex.exp (((t * logNorm x : ℝ) : ℂ) * Complex.I) := by
  have h : ψ x = (χ x * Circle.exp (t * logNorm x))⁻¹ := by
    rw [hp, neg_mul, Circle.exp_neg, mul_inv]
  calc
    star (ψ x : ℂ) = star (((χ x * Circle.exp (t * logNorm x))⁻¹ : Circle) : ℂ) :=
      congrArg (fun c : Circle ↦ star (c : ℂ)) h
    _ = _ := by rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star, Circle.coe_mul, Circle.coe_exp]

local notation "hs0(" hs ")" => (zero_le_one.trans (hs).le : (0:ℝ) ≤ _)
local notation "zeroVec(" χ ", " hs ", " j ")" =>
  (spectralLineJet_memLp χ hs j).toLp (spectralZeroJet (χ (j).val.1) 0 (j).val.2.1 (j).val.2.2)

/-- A bounded extension of an admitted evaluation on one isotype agrees by
density with the ambient Sobolev pairing, up to the Fourier derivative phase. -/
private theorem lineProfile_admitted_functional
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (ξ : PontryaginDual C₁) {a s : ℝ} (hs : 1 < s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ ξ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ ξ, s, hs0(hs))) (he : DenseRange e)
    (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (j : SpectralLineJetIndex χ a s) (hj : j.val.1 = ξ)
    (Λ : StrongDual ℂ Wχ(χ ξ, s, hs0(hs)))
    (hΛ : ∀ p, Λ (e p) = iteratedDeriv j.val.2.2 p j.val.2.1)
    (y : Wχ(χ ξ, s, hs0(hs))) :
    Λ y = Complex.I^j.val.2.2 * spectralSobolevPairing y.val zeroVec(χ, hs, j) := by
  let v := zeroVec(χ, hs, j)
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 0 0 s le_rfl hs0(hs)).exists.choose
  let Φ := T.symm v
  have hpair (x : WI(s)) : Φ x = spectralSobolevPairing x v :=
    (spectralSobolevPairing_dual (le_rfl : (0:ℝ) ≤ 0) hs0(hs) Φ x).2.trans
      (congrArg (spectralSobolevPairing x) (T.apply_symm_apply v))
  have hphase (t : ℝ) (x : C𝔽) : star (γ t x : ℂ) = (χ j.val.1 x : ℂ) *
    Complex.exp (((t*logNorm x : ℝ) : ℂ)*Complex.I) := by
    rw [hj]
    exact lineJet_chart_star (hγ t) x
  let R (z : Wχ(χ ξ, s, hs0(hs))) := Complex.I^j.val.2.2 * Φ z.val
  have hR (p : 𝓢(ℝ, ℂ)) : Λ (e p) = R (e p) := by
    have hhat : (fun t : ℝ ↦ lcaFourier μ𝔽 (e p).val (γ t)) = p := funext fun t ↦
      (integral_congr_ae ((hrep p).mul EventuallyEq.rfl)).trans (hF p t)
    have hd := spectralLineJet_fourier_profile_derivative χ hs j (e p).val γ hphase
    exact (hΛ p).trans (((congrArg (fun q : ℝ → ℂ ↦ iteratedDeriv j.val.2.2 q j.val.2.1) hhat).symm.trans hd).trans
      (congrArg (Complex.I^j.val.2.2 * ·) (hpair (e p).val).symm))
  have hfin : (Λ : Wχ(χ ξ, s, hs0(hs)) → ℂ) = R := he.equalizer Λ.continuous
    (continuous_const.mul (Φ.continuous.comp continuous_subtype_val)) (funext hR)
  exact (congrFun hfin y).trans (congrArg (Complex.I^j.val.2.2 * ·) (hpair y.val))

private theorem lineProfile_all_bounded_jets_vanish
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (ξ : PontryaginDual C₁) {a s : ℝ} (hs : 1 < s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ ξ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (honto : ∀ v : SchwartzBruhat C𝔽, (∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (χ ξ k.val : ℂ) * v x) → ∃ p, P p = v)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ ξ, s, hs0(hs))) (he : DenseRange e)
    (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (y : Wχ(χ ξ, s, hs0(hs)))
    (hy : ∀ j : SpectralLineJetIndex χ a s, j.val.1 = ξ → spectralSobolevPairing y.val zeroVec(χ,hs,j) = 0)
    (t : ℝ) (k : ℕ) (hk : k < (meromorphicOrderAt (continuedCompletedHeckeL (χ ξ)) (shift(a,t))).untop₀.toNat)
    (Λ : StrongDual ℂ Wχ(χ ξ, s, hs0(hs))) (hΛ : ∀ p, Λ (e p) = iteratedDeriv k p t) :
    Λ y = 0 := by
  have hc := lineProfile_jet_endpoint_necessary (χ ξ) s hs0(hs) P γ hγ hF honto e hrep t k Λ hΛ
  let j : SpectralLineJetIndex χ a s := ⟨(ξ,t,k), (lt_spectralBoundaryMultiplicity s _ k).mpr ⟨hk,by linarith⟩⟩
  exact (lineProfile_admitted_functional χ ξ hs P γ hγ hF e he hrep j rfl Λ hΛ y).trans (by rw [hy j rfl,mul_zero])

/-- In a fixed isotype the geometric theta closure contains every vector
annihilated by the continuous derivatives below the Hecke zero orders. -/
private theorem lineProfile_isotype_mem_of_bounded_jets
    (η : PontryaginDual C𝔽) (a s : ℝ) (hs : 0 ≤ s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (η x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (hoff : ∀ p ψ, ψ ∉ range γ → lcaFourier μ𝔽 (P p) ψ = 0)
    (honto : ∀ v : SchwartzBruhat C𝔽, (∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (η k.val : ℂ) * v x) → ∃ p, P p = v)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(η, s, hs)) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (y : Wχ(η, s, hs))
    (hy : ∀ (t : ℝ) (k : ℕ), k < (meromorphicOrderAt (continuedCompletedHeckeL η) (shift(a, t))).untop₀.toNat →
      ∀ Λ : StrongDual ℂ Wχ(η, s, hs), (∀ p, Λ (e p) = iteratedDeriv k p t) → Λ y = 0) :
    y.val ∈ globalThetaSobolev F a (le_rfl : (0 : ℝ) ≤ 0) hs := by
  let m (t : ℝ) := (meromorphicOrderAt (continuedCompletedHeckeL η) (shift(a,t))).untop₀.toNat
  let N := (globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs).comap (Wχ(η, s, hs)).subtype
  have hN : IsClosed (N : Set Wχ(η, s, hs)) := (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  have he := lineProfile_denseEmbedding η s hs P honto e hrep
  have hint := lineProfile_chart_intertwine η s hs P γ hF hoff e hrep
  let U := lineProfile_chart_approximateUnit η s hs P γ hγ hF honto e hint
  let g := U.choose
  let T := U.choose_spec.choose
  have hT := U.choose_spec.choose_spec
  exact schwartzMap_mem_closedSubmodule_of_vanishing_jets m N hN e he
    (fun h _ ↦ lineProfile_chart_multiplier η s hs P e hint h)
    (continuedCompletedHeckeL_finite_vertical_zeros_on_compact η a) (lineProfile_hecke_compactIdeal η a s hs P γ hγ hF hoff e hrep)
    g hT.1 T hT.2.1 hT.2.2 y hy

/-- Reverse norm-closure inclusion inside a single compact-character isotype on
a zero-width spectral line. Each surviving jet of this isotype is tested. -/
private theorem lineProfile_isotype_synthesis_chart
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (ξ : PontryaginDual C₁) {a s : ℝ} (hs : 1 < s)
    (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat C𝔽) (γ : ℝ → PontryaginDual C𝔽)
    (hγ : ∀ t x, γ t x = (χ ξ x)⁻¹ * Circle.exp (-t * logNorm x))
    (hF : ∀ p t, lcaFourier μ𝔽 (P p) (γ t) = p t)
    (hoff : ∀ p ψ, ψ ∉ range γ → lcaFourier μ𝔽 (P p) ψ = 0)
    (honto : ∀ v : SchwartzBruhat C𝔽, (∀ (k : C₁) (x : C𝔽), v (k.val⁻¹*x) = (χ ξ k.val : ℂ) * v x) → ∃ p, P p = v)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] Wχ(χ ξ, s, hs0(hs))) (hrep : ∀ p, ((e p).val : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ))
    (y : Wχ(χ ξ, s, hs0(hs)))
    (hy : ∀ j : SpectralLineJetIndex χ a s, j.val.1 = ξ → spectralSobolevPairing y.val zeroVec(χ,hs,j) = 0) :
    y.val ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs0(hs) := by
  have he := lineProfile_denseEmbedding (χ ξ) s hs0(hs) P honto e hrep
  exact lineProfile_isotype_mem_of_bounded_jets (χ ξ) a s hs0(hs) P γ hγ hF hoff honto e hrep y
    (lineProfile_all_bounded_jets_vanish χ ξ hs P γ hγ hF honto e he hrep y hy)

private theorem lineProfile_isotype_synthesis
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (ξ : PontryaginDual C₁) {a s : ℝ} (hs : 1 < s)
    (y : Wχ(χ ξ, s, hs0(hs)))
    (hy : ∀ j : SpectralLineJetIndex χ a s, j.val.1 = ξ → spectralSobolevPairing y.val zeroVec(χ,hs,j) = 0) :
    y.val ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs0(hs) := by
  let H := exists_schwartzBruhat_mellinFrequencyChart m𝔽 hm𝔽 hms𝔽 μ𝔽 (χ ξ)
  let P := H.choose
  let γ := H.choose_spec.choose
  have h := H.choose_spec.choose_spec
  let E := lineProfile_sobolevLift (χ ξ) s hs0(hs) P h.2.2.2.1
  exact lineProfile_isotype_synthesis_chart χ ξ hs P γ h.1 h.2.1 h.2.2.1 h.2.2.2.2 E.choose E.choose_spec y hy

/-- The character-weighted average of a continuous orbit belongs to its isotype.
Testing this vector against a continuous functional gives the Fourier coefficient
of the scalar orbit. -/
private theorem spectralLineJet_characterAverage {G E : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) (ξ : PontryaginDual G) (y : E) :
    ∃ v ∈ actionIsotype ρ ξ, ∀ φ : StrongDual ℂ E, φ v = ∫ g, star (ξ g : ℂ) * φ (ρ g y) ∂μ := by
  let A (g : G) := star (ξ g : ℂ) • ρ g y
  have hA : Continuous A := (show Continuous (fun g ↦ star (ξ g : ℂ)) by fun_prop).smul
    (hρ.comp (continuous_id.prodMk continuous_const))
  have hi := hA.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace A)
  let v := ∫ g, A g ∂μ
  have hφ (φ : StrongDual ℂ E) : φ v = ∫ g, star (ξ g : ℂ) * φ (ρ g y) ∂μ := by
    refine (φ.integral_comp_comm hi).symm.trans ?_
    exact integral_congr_ae (.of_forall fun g ↦ φ.map_smul _ _)
  refine ⟨v, (mem_actionIsotype ..).mpr fun k ↦ ?_, hφ⟩
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro φ
  have h := hφ (φ.comp (ρ k))
  rw [map_smul, hφ φ, smul_eq_mul, ← integral_const_mul, ← integral_mul_left_eq_self (μ := μ)
    (fun g ↦ (ξ k : ℂ) * (star (ξ g : ℂ) * φ (ρ g y))) k]
  apply h.trans (integral_congr_ae (.of_forall fun g ↦ ?_))
  simp only [ContinuousLinearMap.comp_apply, map_mul, Circle.coe_mul, star_mul', mul_apply_eq_comp]
  rw [mul_assoc (star (ξ k : ℂ)), ← mul_assoc (ξ k : ℂ)]
  simp [← Circle.coe_inv_eq_conj]
/-- A closed subspace containing all character components of a vector contains
the vector itself. Testing its compact orbit against a separating functional
reduces to uniqueness of Fourier coefficients on the compact abelian group. -/
private theorem lineProfile_compact_components {G E J : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.WeaklyRegular] (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) (N : Submodule ℂ E) (hN : IsClosed (N : Set E))
    (Λ : J → StrongDual ℂ E) (y : E) (hy : ∀ g j, Λ j (ρ g y) = 0)
    (hiso : ∀ (ξ : PontryaginDual G) (x : E), x ∈ actionIsotype ρ ξ → (∀ j, Λ j x = 0) → x ∈ N) :
    y ∈ N := by
  by_contra hny
  obtain ⟨φ,hne,hzero⟩ := exists_dual_eq_zero_on_submodule_of_notMem N hN hny
  let u (g : G) := φ (ρ g y)
  have hu : Continuous u := φ.continuous.comp (hρ.comp (continuous_id.prodMk continuous_const))
  have hcoeff (ξ : PontryaginDual G) : ∫ g, star (ξ g : ℂ) * u g ∂μ = 0 := by
    obtain ⟨v, hv, hm⟩ := spectralLineJet_characterAverage μ ρ hρ ξ y
    rw [← hm φ]
    apply hzero _ (hiso ξ v hv ?_)
    intro j
    rw [hm (Λ j)]
    exact integral_eq_zero_of_ae (.of_forall fun g ↦ by simp [hy g j])
  have hae := ae_eq_zero_of_character_integral_eq_zero μ (hu.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hcoeff
  have heq := Measure.eq_of_ae_eq hae hu continuous_const
  exact hne (by simpa [u] using congrFun heq 1)

private theorem lineProfile_raw_normOne (χ : PontryaginDual C𝔽) (t : ℝ) (n : ℕ) (g : C₁) (x : C𝔽) :
    spectralZeroJet χ 0 t n (g.val*x) = (χ g.val : ℂ) * spectralZeroJet χ 0 t n x := by
  have hm : ideleClassNorm F (g.val*x) = ideleClassNorm F x := by rw [map_mul,g.property,one_mul]
  have hl : logNorm (g.val*x) = logNorm x := congrArg (fun z : ℝ≥0ˣ ↦ Real.log (z.val : ℝ)) hm
  rw [lineJet_as_phase,lineJet_as_phase,hl,map_mul,Circle.coe_mul]
  ring

private theorem lineProfile_integral_eigen {G : Type*} [CommGroup G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (r f : G → ℂ) (g : G) (c : ℂ)
    (hr : ∀ x, r (g*x) = c * r x) :
    (∫ x, f (g⁻¹*x) * r x ∂μ) = c * ∫ x, f x * r x ∂μ := by
  rw [← integral_const_mul]
  refine (integral_mul_left_eq_self (μ := μ) (fun x ↦ f (g⁻¹*x) * r x) g).symm.trans ?_
  apply integral_congr_ae
  refine .of_forall fun x ↦ ?_
  change f (g⁻¹*(g*x)) * r (g*x) = c*(f x*r x)
  rw [inv_mul_cancel_left,hr]
  ring

private theorem lineProfile_jet_normOne_dual
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s)
    (j : SpectralLineJetIndex χ a s) : ∃ Λ : StrongDual ℂ WI(s),
      (∀ u, Λ u = spectralSobolevPairing u zeroVec(χ,hs,j)) ∧
      (∀ (g : C₁) u, Λ (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs0(hs) g.val u) =
        (χ j.val.1 g.val : ℂ) * Λ u) ∧
      ∀ u, Λ u = ∫ x, u x * spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2 x ∂μ𝔽 := by
  let r := spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
  let v := zeroVec(χ,hs,j)
  let H := spectralLineJet_functional χ hs j
  let Λ := H.choose
  have hΛ (u : WI(s)) : Λ u = ∫ x, u x * r x ∂μ𝔽 := (H.choose_spec.1 u).2
  have hv : (v : C𝔽 → ℂ) =ᵐ[μ𝔽] r := by
    have hL : Measurable logNorm := (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).measurable.log
    have hac : μ𝔽 ≪ (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm x))⁻¹) :=
      withDensity_absolutelyContinuous' (((continuous_intervalSobolevDensity' 0 0 s).measurable.comp hL).inv.ennreal_ofReal.aemeasurable)
        (.of_forall fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (intervalSobolevDensity_pos 0 0 s _)))
    exact hac.ae_eq (MemLp.coeFn_toLp _)
  refine ⟨Λ,fun u ↦ (hΛ u).trans (integral_congr_ae (EventuallyEq.rfl.mul hv.symm)),(fun g u ↦ ?_), hΛ⟩
  rw [hΛ,hΛ]
  have htr := hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s le_rfl hs0(hs) g.val u
  exact (integral_congr_ae (htr.mul EventuallyEq.rfl)).trans (lineProfile_integral_eigen μ𝔽 r u g.val _
    (lineProfile_raw_normOne (χ j.val.1) j.val.2.1 j.val.2.2 g))

/-- The common zero-jet kernel lies in the global weighted theta closure once that
inclusion is known on each compact-character isotype. -/
private theorem lineProfile_reverse_of_isotypes (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s)
    (hiso : ∀ (ξ : PontryaginDual C₁) (z : Wχ(χ ξ, s, hs0(hs))),
      (∀ j : SpectralLineJetIndex χ a s, j.val.1 = ξ → spectralSobolevPairing z.val zeroVec(χ,hs,j) = 0) →
      z.val ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs0(hs))
    (y : WI(s)) (hy : ∀ j : SpectralLineJetIndex χ a s, spectralSobolevPairing y zeroVec(χ,hs,j) = 0) :
    y ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs0(hs) := by
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let κ : Measure C₁ := Measure.haar
  let : κ.IsHaarMeasure := inferInstanceAs (Measure.haar (G := C₁)).IsHaarMeasure
  let ρ := (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs0(hs)).comp (ideleClassNorm F).ker.subtype
  have hρ : Continuous (fun p : C₁ × WI(s) ↦ ρ p.1 p.2) :=
    (exists_hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs0(hs)).choose_spec.2.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let Λ (j : SpectralLineJetIndex χ a s) := (lineProfile_jet_normOne_dual χ hs j).choose
  have hΛ (j : SpectralLineJetIndex χ a s) := (lineProfile_jet_normOne_dual χ hs j).choose_spec
  apply lineProfile_compact_components κ ρ hρ _ (Submodule.isClosed_topologicalClosure _) Λ y
  · intro g j
    exact ((hΛ j).2.1 g y).trans (by rw [(hΛ j).1 y,hy j,mul_zero])
  · intro ξ z hz hAll
    have hz' : z ∈ Wχ(χ ξ, s, hs0(hs)) := by
      change z ∈ actionIsotype ρ ((χ ξ).comp restriction)
      rw [hχ ξ]
      exact hz
    exact hiso ξ ⟨z,hz'⟩ (fun j _ ↦ ((hΛ j).1 z).symm.trans (hAll j))

/-- At width zero the separating compact-character argument assembles the
local multiplier synthesis for every character into ambient norm closure. -/
private theorem spectralLineJet_commonKernel_reverse_proved (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s)
    (y : WI(s)) (hy : ∀ j : SpectralLineJetIndex χ a s, spectralSobolevPairing y zeroVec(χ,hs,j) = 0) :
    y ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs0(hs) :=
  lineProfile_reverse_of_isotypes χ hχ hs (fun ξ ↦ lineProfile_isotype_synthesis χ ξ hs) y hy

private theorem spectralLineJet_commonKernel_forward_proved (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a s : ℝ} (hs : 1 < s) (y : WI(s)) (hy : y ∈ globalThetaSobolev F a (le_rfl : (0:ℝ) ≤ 0) hs0(hs))
    (j : SpectralLineJetIndex χ a s) : spectralSobolevPairing y zeroVec(χ,hs,j) = 0 := by
  let H := lineProfile_jet_normOne_dual χ hs j
  let Λ := H.choose
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 s le_rfl hs0(hs)).exists.choose
  have hgen (f : adelePolarSubspace F) : Λ (E (Submodule.Quotient.mk f)) = 0 := by
    have hE := (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 s le_rfl hs0(hs)).exists.choose_spec.2 f
    have hk := ((lt_spectralBoundaryMultiplicity s _ _).mp j.property).1
    have hm := stripTheta_weighted_moment_zero (χ j.val.1) f a 0 j.val.2.1 j.val.2.2 (by simpa only [add_zero] using hk)
    exact (H.choose_spec.2.2 _).trans ((integral_congr_ae (hE.mul EventuallyEq.rfl)).trans hm)
  have hR : E.toLinearMap.range ≤ Λ.ker := by
    rintro _ ⟨v, rfl⟩
    induction v using Submodule.Quotient.induction_on with
    | H f => exact hgen f
  exact (H.choose_spec.1 y).symm.trans ((E.toLinearMap.range.topologicalClosure_minimal hR Λ.isClosed_ker) hy)

/-- At degree at most one no derivative on a frequency line is continuous in
the weighted norm. Even the values at Hecke zeros impose no closed condition. -/
private theorem lineProfile_lowDegree_mem (χ : PontryaginDual C𝔽) (a s : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ 1) (y : Wχ(χ, s, hs)) :
    y.val ∈ globalThetaSobolev F a (le_rfl : (0 : ℝ) ≤ 0) hs := by
  obtain ⟨P, γ, hγ, hF, hoff, hiso, honto⟩ :=
    exists_schwartzBruhat_mellinFrequencyChart m𝔽 hm𝔽 hms𝔽 μ𝔽 χ
  obtain ⟨e, hrep⟩ := lineProfile_sobolevLift χ s hs P hiso
  apply lineProfile_isotype_mem_of_bounded_jets χ a s hs P γ hγ hF hoff honto e hrep y
  intro t k _ Λ hΛ
  have h := lineProfile_jet_endpoint_necessary χ s hs P γ hγ hF honto e hrep t k Λ hΛ
  linarith [Nat.cast_nonneg (α := ℝ) k]

/-- Paper: Theorem 10.2.2.1, p. 446, at width zero and degree at most one.
The polar-free theta classes are dense at every real center.
Deviation: With the strict endpoint cutoff the jet family is empty, including
at degree one. No chart derivative extends continuously to this Sobolev space. -/
theorem globalThetaSobolev_line_eq_top_of_le_one (a s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) :
    globalThetaSobolev F a (le_rfl : (0 : ℝ) ≤ 0) hs = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice F
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let κ : Measure C₁ := Measure.haar
  let : κ.IsHaarMeasure := inferInstanceAs (Measure.haar (G := C₁)).IsHaarMeasure
  let ρ := (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).comp (ideleClassNorm F).ker.subtype
  have hρ : Continuous (fun p : C₁ × WI(s) ↦ ρ p.1 p.2) :=
    (exists_hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).choose_spec.2.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  apply lineProfile_compact_components (J := Empty) κ ρ hρ _ (Submodule.isClosed_topologicalClosure _)
    Empty.elim y (fun _ j ↦ j.elim)
  intro ξ z hz _
  have hz' : z ∈ Wχ(χ ξ, s, hs) := by
    change z ∈ actionIsotype ρ ((χ ξ).comp restriction)
    rw [hχ ξ]
    exact hz
  exact lineProfile_lowDegree_mem (χ ξ) a s hs hs' ⟨z, hz'⟩

end LineThetaSynthesis

/-- Paper: Theorem 10.2.1.1, pp. 440–443. The weighted theta closure is
the common kernel of the admitted line jets.
Deviation: Compact frequency localization and the strict Sobolev jet cutoff supply the line approximation used on p. 443. -/
private theorem spectralLineJet_commonKernel_direct (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let u : SpectralLineJetIndex χ a s → W'(0, 0, s) := lineU(χ, hs)
    JetKernel(a, le_rfl (a := (0 : ℝ)), lineHs(hs), u) := by
  intro u y
  exact ⟨fun hy ↦ spectralLineJet_commonKernel_forward_proved χ hs y hy,
    spectralLineJet_commonKernel_reverse_proved χ _hχ hs y⟩

section LineJetInterpolation

open scoped SchwartzMap ContDiff Classical

local notation "pair(" f ", " u ")" => spectralSobolevPairing (F := F) f u

/-- A Schwartz profile on one Mellin line gives exactly the corresponding
Sobolev jet moments. The inverse character in the chart accounts for the
conjugation in the Fourier transform. -/
private theorem spectralLineJet_realize_profile
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {a s : ℝ} (hs : 1 < s) (ξ : PontryaginDual C₁) (p : 𝓢(ℝ, ℂ)) :
    ∃ f : W(0, 0, s), ∀ j : SpectralLineJetIndex χ a s,
      Complex.I ^ j.val.2.2 * pair(f, (lineU(χ, hs)) j) =
        if j.val.1 = ξ then iteratedDeriv j.val.2.2 p j.val.2.1 else 0 := by
  classical
  obtain ⟨P, γ, hγ, hP, hzero, _, _⟩ :=
    exists_schwartzBruhat_mellinFrequencyChart m𝔽 hm𝔽 hms𝔽 μ𝔽 (χ ξ)
  obtain ⟨e, he⟩ := exists_modulatedFrequencyLine m𝔽 hm𝔽 hms𝔽
  let ν := (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm x)))
  have hν : ν = sobolevMeasure μ𝔽 (modulatedSobolevWeight m𝔽) s :=
    intervalSobolev_zero_eq_sobolevMeasure m𝔽 μ𝔽 s
  have hmem : MemLp (P p : C𝔽 → ℂ) 2 ν :=
    hν.symm ▸ SchwartzBruhat.memLp_modulatedSobolev μ𝔽 m𝔽 (P p) s (zero_lt_one.trans hs).le
  let f : W(0, 0, s) := hmem.toLp (P p)
  have hle : μ𝔽 ≤ ν := by
    calc
      μ𝔽 = (μ𝔽).withDensity 1 := withDensity_one.symm
      _ ≤ ν := withDensity_mono (.of_forall fun x ↦ by
        change 1 ≤ ENNReal.ofReal (intervalSobolevDensity 0 0 s _)
        rw [ENNReal.one_le_ofReal]
        simpa [intervalSobolevDensity] using Real.one_le_rpow
          (le_add_of_nonneg_right (sq_nonneg _)) (by linarith : 0 ≤ s / 2))
  have hrep : (f : C𝔽 → ℂ) =ᵐ[μ𝔽] (P p : C𝔽 → ℂ) := hle.absolutelyContinuous.ae_eq hmem.coeFn_toLp
  have hFourier (ψ : PontryaginDual C𝔽) : lcaFourier μ𝔽 f ψ = lcaFourier μ𝔽 (P p) ψ :=
    integral_congr_ae (hrep.mul Filter.EventuallyEq.rfl)
  refine ⟨f, fun j ↦ ?_⟩
  let Ψ (t : ℝ) := (χ j.val.1 * (e (Multiplicative.ofAdd t)).val)⁻¹
  have hΨ (t : ℝ) (g : C𝔽) : star (Ψ t g : ℂ) = (χ j.val.1 g : ℂ) *
      Complex.exp (((t * logNorm g : ℝ) : ℂ) * Complex.I) := by
    change star (((χ j.val.1 g * (e (Multiplicative.ofAdd t)).val g)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star, Circle.coe_mul, he, Circle.coe_exp]
    rfl
  rw [← spectralLineJet_fourier_profile_derivative χ hs j f Ψ hΨ]
  by_cases hj : j.val.1 = ξ
  · have hval (t : ℝ) : lcaFourier μ𝔽 f (Ψ t) = p t := by
      have hline : Ψ t = γ t := PontryaginDual.ext fun g ↦ by
        change (χ j.val.1 g * (e (Multiplicative.ofAdd t)).val g)⁻¹ = γ t g
        rw [hγ, hj, he, neg_mul, Circle.exp_neg, mul_inv]
      rw [hFourier, hline, hP]
    rw [ite_eq_left hj, show (fun t ↦ lcaFourier μ𝔽 f (Ψ t)) = (p : ℝ → ℂ) from funext hval]
  · have hval (t : ℝ) : lcaFourier μ𝔽 f (Ψ t) = 0 := by
      rw [hFourier]
      apply hzero
      rintro ⟨u, hu⟩
      apply hj
      apply PontryaginDual.ext
      intro k
      have h := DFunLike.congr_fun hu k.val
      have hk := (mem_lcaAnnihilator_iff _ _).mp (e (Multiplicative.ofAdd t)).property k
      have hjk : χ j.val.1 k = j.val.1 k := DFunLike.congr_fun (hχ j.val.1) k
      have hξk : χ ξ k = ξ k := DFunLike.congr_fun (hχ ξ) k
      change γ u k.val = (χ j.val.1 k.val * (e (Multiplicative.ofAdd t)).val k.val)⁻¹ at h
      rw [hγ] at h
      change (χ ξ k.val)⁻¹ * Circle.exp (-u * logNorm k.val) = _ at h
      rw [show logNorm k.val = 0 by change Real.log ((ideleClassNorm F k.val).val : ℝ) = 0; rw [k.property]; simp,
        mul_zero, Circle.exp_zero, mul_one, hξk, hk, mul_one, hjk] at h
      exact (inv_injective h).symm
    rw [ite_eq_right hj, show (fun t ↦ lcaFourier μ𝔽 f (Ψ t)) = (0 : ℝ → ℂ) from funext hval]
    simp

/-- A smooth compactly supported frequency profile can prescribe a single
Taylor coefficient on a locally finite real set. All remaining jets vanish. -/
private theorem exists_isolated_line_profile {Z : Set ℝ}
    (hZ : ∀ K : Set ℝ, IsCompact K → {x ∈ K | x ∈ Z}.Finite) (c : ℝ) (m : ℕ) :
    ∃ p : 𝓢(ℝ, ℂ), HasCompactSupport (p : ℝ → ℂ) ∧
      (∀ n, iteratedDeriv n p c = if n = m then Complex.I ^ m else 0) ∧
      ∀ x ∈ Z, x ≠ c → (p : ℝ → ℂ) =ᶠ[𝓝 x] 0 := by
  let bad := {x ∈ Metric.closedBall c 1 | x ∈ Z} \ {c}
  let U := Metric.ball c 1 ∩ badᶜ
  have hU : IsOpen U := Metric.isOpen_ball.inter
    ((hZ _ (isCompact_closedBall c 1)).sdiff (t := {c})).isClosed.isOpen_compl
  have hc : c ∈ U := ⟨Metric.mem_ball_self zero_lt_one, fun h ↦ h.2 rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hc)
  let B : ContDiffBump c := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let A := Complex.I ^ m / (m.factorial : ℂ)
  let P (x : ℝ) := (x - c) ^ m • A
  let f (x : ℝ) := B x • P x
  have hsupport : HasCompactSupport f := B.hasCompactSupport.smul_right
  have hf : ContDiff ℝ (∞) f := B.contDiff.smul (((contDiff_id.sub contDiff_const).pow m).smul contDiff_const)
  refine ⟨hsupport.toSchwartzMap hf, hsupport, ?_, ?_⟩
  · intro n
    have heq : f =ᶠ[𝓝 c] P := B.eventuallyEq_one.mono fun x hx ↦ by
      change B x • P x = P x
      rw [show B x = 1 from hx, one_smul]
    change iteratedDeriv n f c = _
    rw [heq.iteratedDeriv_eq n]
    have hder : iteratedDeriv n (fun x : ℝ ↦ (x-c)^m) c = if n = m then (m.factorial : ℝ) else 0 := by
      rw [iteratedDeriv_comp_sub_const n (fun x : ℝ ↦ x^m) c]
      simpa using (iteratedDeriv_fun_pow_zero (𝕜 := ℝ) (m := m) (n := n))
    rw [show iteratedDeriv n P c = _ from iteratedDeriv_smul_const (f := fun x : ℝ ↦ (x-c)^m)
      (by fun_prop) A, hder]
    split_ifs with h
    · rw [Complex.real_smul]
      push_cast
      dsimp [A]
      field_simp [Nat.factorial_ne_zero]
    · exact zero_smul _ _
  · intro x hx hxc
    change f =ᶠ[𝓝 x] 0
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro h
    have hB : x ∈ tsupport B := tsupport_smul_subset_left _ _ h
    rw [B.tsupport_eq] at hB
    have hu := hball (Metric.closedBall_subset_ball (by dsimp [B]; linarith : B.rOut < r) hB)
    exact hu.2 ⟨⟨Metric.ball_subset_closedBall hu.1, hx⟩, hxc⟩

/-- Paper: Theorem 10.2.1.1, pp. 440–443. Each surviving zero jet on the
a-line has a Sobolev vector pairing to one with it and to zero with every other jet.
The construction prescribes a compact smooth frequency profile on one character. -/
private theorem exists_lineJet_single_interpolant
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {a s : ℝ} (hs : 1 < s) (i : SpectralLineJetIndex χ a s) :
    ∃ f : W(0, 0, s), ∀ j : SpectralLineJetIndex χ a s,
      pair(f, (lineU(χ, hs)) j) = if j = i then 1 else 0 := by
  classical
  let Z := {t : ℝ | 0 < (meromorphicOrderAt (continuedCompletedHeckeL (χ i.val.1))
    (shift(a,t))).untop₀.toNat}
  have hZ (K : Set ℝ) (hK : IsCompact K) : {t ∈ K | t ∈ Z}.Finite :=
    continuedCompletedHeckeL_finite_vertical_zeros_on_compact (χ i.val.1) a K hK
  obtain ⟨p, _, hp, hother⟩ := exists_isolated_line_profile hZ i.val.2.1 i.val.2.2
  obtain ⟨f, hf⟩ := spectralLineJet_realize_profile χ hχ hs i.val.1 p
  refine ⟨f, fun j ↦ ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero j.val.2.2 Complex.I_ne_zero)
  rw [hf]
  by_cases hij : j = i
  · subst j
    simp [hp]
  · rw [ite_eq_right hij, mul_zero]
    by_cases hξ : j.val.1 = i.val.1
    · rw [ite_eq_left hξ]
      by_cases ht : j.val.2.1 = i.val.2.1
      · rw [ht, hp]
        have hdeg : j.val.2.2 ≠ i.val.2.2 := fun h ↦ hij (Subtype.ext (Prod.ext hξ (Prod.ext ht h)))
        simp [hdeg]
      · have hjZ : j.val.2.1 ∈ Z := by
          have hm : 0 < (meromorphicOrderAt (continuedCompletedHeckeL (χ j.val.1))
              (shift(a,j.val.2.1))).untop₀.toNat :=
            Nat.zero_lt_of_lt (lt_of_lt_of_le j.property (min_le_left _ _))
          change 0 < (meromorphicOrderAt (continuedCompletedHeckeL (χ i.val.1)) (shift(a,j.val.2.1))).untop₀.toNat
          simpa only [hξ] using hm
        simpa using (hother _ hjZ ht).iteratedDeriv_eq j.val.2.2
    · simp [hξ]

/-- Compact Fourier support meets only finitely many surviving line jets. The
restriction to the compact norm-one subgroup is discrete, each real chart is
closed, and the positive Hecke divisor has finite support on every compact set. -/
private theorem lineJet_compact_frequencies
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (e : Multiplicative ℝ ≃ₜ* lcaAnnihilator (ideleClassNorm F).ker)
    (a s : ℝ) (K : Set (PontryaginDual C𝔽)) (hK : IsCompact K) :
    {j : SpectralLineJetIndex χ a s |
      ((χ j.val.1) * (e (Multiplicative.ofAdd j.val.2.1)).val)⁻¹ ∈ K}.Finite := by
  classical
  let H := (ideleClassNorm F).ker
  have hHH : IsCompact (H : Set C𝔽) := IsModulation.isCompact_ker (m := m𝔽) hm𝔽
  let : CompactSpace C₁ := isCompact_iff_compactSpace.mp hHH
  let r := PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* C𝔽)
  let A := (fun ψ ↦ (r ψ)⁻¹) '' K
  have hA : A.Finite := (hK.image r.continuous.inv).finite_of_discrete
  let Ψ (ξ : PontryaginDual C₁) (t : ℝ) := (χ ξ * (e (Multiplicative.ofAdd t)).val)⁻¹
  have hΨ (ξ : PontryaginDual C₁) : Topology.IsClosedEmbedding (Ψ ξ) :=
    (Homeomorph.inv (PontryaginDual C𝔽)).isClosedEmbedding.comp
      ((Homeomorph.mulLeft (χ ξ)).isClosedEmbedding.comp
        (((lcaAnnihilator H).isClosed_of_isOpen (isOpen_lcaAnnihilator _ hHH)).isClosedEmbedding_subtypeVal.comp
          e.toHomeomorph.isClosedEmbedding))
  have hr (ξ : PontryaginDual C₁) (t : ℝ) : (r (Ψ ξ t))⁻¹ = ξ := by
    apply PontryaginDual.ext
    intro k
    have hfk := (mem_lcaAnnihilator_iff _ _).mp (e (Multiplicative.ofAdd t)).property k
    change ((χ ξ k * (e (Multiplicative.ofAdd t)).val k)⁻¹)⁻¹ = ξ k
    rw [hfk, mul_one, inv_inv]
    exact DFunLike.congr_fun (hχ ξ) k
  let N (ξ : PontryaginDual C₁) (t : ℝ) :=
    (meromorphicOrderAt (continuedCompletedHeckeL (χ ξ)) (shift(a,t))).untop₀.toNat
  let T (ξ : PontryaginDual C₁) := {t ∈ (Ψ ξ) ⁻¹' K | 0 < N ξ t}
  have hT (ξ) : (T ξ).Finite :=
    continuedCompletedHeckeL_finite_vertical_zeros_on_compact (χ ξ) a _ ((hΨ ξ).isCompact_preimage hK)
  let J := SpectralLineJetIndex χ a s
  let S : Set J := {j | Ψ j.val.1 j.val.2.1 ∈ K}
  let π (j : J) := (j.val.1, j.val.2.1)
  change S.Finite
  apply Set.Finite.of_finite_fibers π
  · apply (hA.biUnion (fun ξ _ ↦ (hT ξ).image (Prod.mk ξ))).subset
    rintro _ ⟨j, hj, rfl⟩
    have hξ : j.val.1 ∈ A := ⟨Ψ j.val.1 j.val.2.1, hj, hr _ _⟩
    exact Set.mem_iUnion₂.mpr ⟨_, hξ, j.val.2.1, ⟨hj,
      Nat.zero_lt_of_lt (lt_of_lt_of_le j.property (min_le_left _ _))⟩, rfl⟩
  · rintro ⟨ξ,t⟩ _
    apply (Set.finite_lt_nat (spectralBoundaryMultiplicity s (N ξ t))).of_injOn (f := fun j : J ↦ j.val.2.2)
    · intro j hj
      have eq : π j = (ξ,t) := hj.2
      exact (congrArg (fun v : PontryaginDual C₁ × ℝ ↦
        j.val.2.2 < spectralBoundaryMultiplicity s (N v.1 v.2)) eq).mp j.property
    · rintro i hi j hj heq
      have eij : π i = π j := (show π i = (ξ,t) from hi.2).trans (show π j = (ξ,t) from hj.2).symm
      have hξ : i.val.1 = j.val.1 := congrArg (fun x : PontryaginDual C₁ × ℝ ↦ x.1) eij
      have ht : i.val.2.1 = j.val.2.1 := congrArg (fun x : PontryaginDual C₁ × ℝ ↦ x.2) eij
      exact Subtype.ext (Prod.ext hξ (Prod.ext ht heq))

private theorem lineJet_test_integrable
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s)
    (i : SpectralLineJetIndex χ a s) (f : W(0, 0, s)) : Integrable (f : C𝔽 → ℂ) μ𝔽 := by
  let j : SpectralLineJetIndex χ a s := ⟨(i.val.1, i.val.2.1, 0), Nat.zero_lt_of_lt i.property⟩
  have h := ((spectralLineJet_functional χ hs j).choose_spec.1 f).1
  refine h.norm.mono' (Lp.stronglyMeasurable f).aestronglyMeasurable (.of_forall fun x ↦ ?_)
  change ‖f x‖ ≤ ‖f x * spectralZeroJet (χ i.val.1) 0 i.val.2.1 0 x‖
  rw [lineJet_as_phase]
  simp only [norm_mul, pow_zero, mul_one, Circle.norm_coe, Complex.norm_exp_ofReal_mul_I, le_refl]

/-- A representative with compact Fourier support can have only finitely many
nonzero line jet moments. -/
private theorem lineJet_finite_moments_of_compact_fourier
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {a s : ℝ} (hs : 1 < s) (f : W(0, 0, s)) (K : Set (PontryaginDual C𝔽)) (hK : IsCompact K)
    (hz : ∀ ψ ∉ K, lcaFourier μ𝔽 f ψ = 0) :
    (support (fun j : SpectralLineJetIndex χ a s ↦ pair(f, (lineU(χ, hs)) j))).Finite := by
  obtain ⟨e, he⟩ := exists_modulatedFrequencyLine m𝔽 hm𝔽 hms𝔽
  apply (lineJet_compact_frequencies χ hχ e a s K hK).subset
  intro j hj
  by_contra h
  let Ψ (t : ℝ) := (χ j.val.1 * (e (Multiplicative.ofAdd t)).val)⁻¹
  have hΨ (t : ℝ) (g : C𝔽) : star (Ψ t g : ℂ) = (χ j.val.1 g : ℂ) *
      Complex.exp (((t * logNorm g : ℝ) : ℂ) * Complex.I) := by
    change star (((χ j.val.1 g * (e (Multiplicative.ofAdd t)).val g)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star, Circle.coe_mul, he, Circle.coe_exp]
    rfl
  have hc : Continuous Ψ :=
    (continuous_const.mul (continuous_subtype_val.comp e.continuous)).inv
  have hmem : ∀ᶠ t in 𝓝 j.val.2.1, Ψ t ∈ Kᶜ := (hK.isClosed.isOpen_compl.preimage hc).mem_nhds h
  have hzero : (fun t ↦ lcaFourier μ𝔽 f (Ψ t)) =ᶠ[𝓝 j.val.2.1] 0 :=
    hmem.mono fun t ht ↦ hz _ ht
  have heval := (spectralLineJet_fourier_profile_derivative χ hs j f Ψ hΨ).symm.trans
    (hzero.iteratedDeriv_eq j.val.2.2)
  have hprod : Complex.I ^ j.val.2.2 * pair(f, (lineU(χ, hs)) j) = 0 := by simpa using heval
  exact hj ((mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ Complex.I_ne_zero))

/-- A continuous representative of a Fourier transform vanishes off the
topological support of any almost-everywhere equal representative. -/
private theorem lineJet_zero_off_rep {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (ν : Measure X) [ν.IsOpenPosMeasure] {f g : X → ℂ}
    (hf : Continuous f) (heq : f =ᵐ[ν] g) :
    ∀ x ∉ tsupport g, f x = 0 := by
  let U := (tsupport g)ᶜ
  have hU : IsOpen U := (isClosed_tsupport g).isOpen_compl
  have hae : f =ᵐ[ν.restrict U] 0 := by
    filter_upwards [ae_restrict_of_ae heq, ae_restrict_mem hU.measurableSet] with x hx hxin
    exact hx.trans (image_eq_zero_of_notMem_tsupport hxin)
  exact fun x hx ↦ Measure.eqOn_open_of_ae_eq hae hU hf.continuousOn continuousOn_const hx

private theorem lineJet_dense_compact_moments
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (a : ℝ) {s : ℝ} (hs : 1 < s) :
    Dense {f : W(0, 0, s) | (support (fun j : SpectralLineJetIndex χ a s ↦ pair(f, (lineU(χ, hs)) j))).Finite} := by
  classical
  let J := SpectralLineJetIndex χ a s
  by_cases hJ : Nonempty J
  swap
  · have : IsEmpty J := not_nonempty_iff.mp hJ
    exact dense_univ.mono fun f _ ↦ Set.toFinite _
  let : MeasurableSpace (PontryaginDual C𝔽) := borel _
  let : BorelSpace (PontryaginDual C𝔽) := ⟨rfl⟩
  obtain ⟨ν,hν,-⟩ := lcaPlancherelMeasure_existsUnique μ𝔽
  let : ν.IsHaarMeasure := hν.1
  let U := (lcaFourier_unitary μ𝔽 ν hν).exists.choose
  let D (w : Measure C𝔽) := {f : Lp ℂ 2 w | ∃ (u : Lp ℂ 2 μ𝔽) (v : PontryaginDual C𝔽 → ℂ),
    (u : C𝔽 → ℂ) =ᵐ[μ𝔽] (f : C𝔽 → ℂ) ∧ (U u : PontryaginDual C𝔽 → ℂ) =ᵐ[ν] v ∧ HasCompactSupport v}
  let w := (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm x)))
  have hw : w = sobolevMeasure μ𝔽 (modulatedSobolevWeight m𝔽) s :=
    intervalSobolev_zero_eq_sobolevMeasure m𝔽 μ𝔽 s
  have hd : Dense (D w) := (congrArg (fun v ↦ Dense (D v)) hw).mpr
    (dense_modulatedSobolev_fourierCompactSupport μ𝔽 m𝔽 ν hν hm𝔽 hms𝔽 s (by linarith))
  apply hd.mono
  rintro f ⟨u,v,hu,huv,hv⟩
  have hi := lineJet_test_integrable χ hs hJ.some f
  have hpl := (lcaFourier_unitary μ𝔽 ν hν).exists.choose_spec u (hi.congr hu.symm) (Lp.memLp u)
  rw [Lp.toLp_coeFn] at hpl
  have hFu : lcaFourier μ𝔽 f = lcaFourier μ𝔽 u :=
    funext fun ψ ↦ integral_congr_ae (hu.symm.mul Filter.EventuallyEq.rfl)
  have hae : lcaFourier μ𝔽 f =ᵐ[ν] v := hFu ▸ hpl.symm.trans huv
  obtain ⟨f₀,hf₀⟩ := lcaFourier_zeroAtInfty μ𝔽 hi
  have hc : Continuous (lcaFourier μ𝔽 f) := (funext hf₀) ▸ f₀.continuous
  exact lineJet_finite_moments_of_compact_fourier χ hχ hs f _ hv (lineJet_zero_off_rep ν hc hae)

/-- Finite moment support gives a finite interpolant modulo the joint kernel.
When such inputs are dense, the quotient images of single-coordinate
interpolants have dense span. -/
private theorem dense_span_biorthogonal_of_finite_support
    {J E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q] (q : E →L[ℂ] Q) (hq : Surjective q)
    (v : J → E) (l : J → E →ₗ[ℂ] ℂ)
    (hv : ∀ i j, l j (v i) = if i = j then 1 else 0)
    (hk : ∀ x, (∀ j, l j x = 0) → q x = 0)
    (hd : Dense {x : E | (Function.support (fun j ↦ l j x)).Finite}) :
    Dense (Submodule.span ℂ (range (fun i ↦ q (v i))) : Set Q) := by
  classical
  apply hq.denseRange.dense_of_mapsTo q.continuous hd
  intro x hx
  let S := hx.toFinset
  let y := ∑ i ∈ S, l i x • v i
  have hly (j : J) : l j y = l j x := by
    change l j (∑ i ∈ S, _) = _
    simp only [map_sum, map_smul, hv, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq']
    by_cases hj : j ∈ S
    · simp [hj]
    · have hz : l j x = 0 := by
        by_contra hn
        exact hj (hx.mem_toFinset.mpr hn)
      simp [hj, hz]
  have hxy : q x = q y := sub_eq_zero.mp (by
    rw [← map_sub]
    exact hk _ fun j ↦ by rw [map_sub, hly, sub_self])
  rw [hxy]
  change q (∑ i ∈ S, l i x • v i) ∈ Submodule.span ℂ _
  rw [map_sum]
  exact Submodule.sum_mem _ fun i hi ↦ (q.map_smul _ _).symm ▸
    (Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i)))

private theorem lineJet_dense_interpolants_of_reverse
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {a s : ℝ} (hs : 1 < s)
    (hk : ∀ f : W(0, 0, s), (∀ j : SpectralLineJetIndex χ a s, pair(f, (lineU(χ, hs)) j) = 0) →
      f ∈ globalThetaSobolev F a (le_rfl : (0 : ℝ) ≤ 0) (zero_lt_one.trans hs).le) :
    let J := SpectralLineJetIndex χ a s
    let Θ := globalThetaSobolev F a (le_rfl : (0 : ℝ) ≤ 0) (zero_lt_one.trans hs).le
    ∃ v : J → W(0, 0, s), (∀ i, pair(v i, (lineU(χ, hs)) i) = 1) ∧
      (∀ i j, i ≠ j → pair(v i, (lineU(χ, hs)) j) = 0) ∧
      Dense (Submodule.span ℂ (range (fun i ↦ Θ.mkQ (v i))) : Set (W(0, 0, s) ⧸ Θ)) := by
  intro J Θ
  classical
  choose v hv using exists_lineJet_single_interpolant χ hχ (a := a) hs
  refine ⟨v, fun i ↦ by simpa using hv i i, fun i j h ↦ by simpa [Ne.symm h] using hv i j, ?_⟩
  let hs0 := (zero_lt_one.trans hs).le
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 0 0 s le_rfl hs0).exists.choose
  let u (j : J) := (spectralLineJet_memLp χ hs j).toLp (spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2)
  let l (j : J) := (T.symm (u j)).toLinearMap
  have hl (j : J) (f : W(0, 0, s)) : l j f = pair(f, (lineU(χ, hs)) j) := by
    have h := (spectralSobolevPairing_dual le_rfl hs0 (T.symm (u j)) f).2
    exact h.trans (congrArg (spectralSobolevPairing f) (T.apply_symm_apply _))
  apply dense_span_biorthogonal_of_finite_support Θ.mkQL Θ.mkQ_surjective v l
  · intro i j
    rw [hl, hv]
    by_cases he : i = j
    · subst j
      simp
    · simp [he, Ne.symm he]
  · intro f hf
    exact (spectralSobolevQuotient_eq_zero a le_rfl hs0 f).mpr (hk f (fun j ↦ (hl j f).symm.trans (hf j)))
  · apply (lineJet_dense_compact_moments χ hχ a hs).mono
    intro f hf
    change (support (fun j : J ↦ l j f)).Finite
    have hfun : (fun j : J ↦ l j f) = (fun j : J ↦ pair(f, (lineU(χ, hs)) j)) :=
      funext fun j ↦ hl j f
    rw [hfun]
    exact hf

end LineJetInterpolation

/-- Paper: Theorem 10.2.1.1, pp. 440–443. Single-jet interpolants have
representatives whose images span a dense subspace of the line quotient.
Deviation: Use the strict Sobolev cutoff. Smooth profiles on one real
frequency line give the individual interpolants. Compact Fourier support
and the line common-kernel identity give norm density in the quotient. -/
private theorem spectralLineJet_denseInterpolants_direct (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let J := SpectralLineJetIndex χ a s
    let u : J → W'(0, 0, s) := lineU(χ, hs)
    JetInterpolation(J, a, le_rfl (a := (0 : ℝ)), lineHs(hs), u) := by
  exact lineJet_dense_interpolants_of_reverse χ _hχ hs
    (fun f ↦ (spectralLineJet_commonKernel_direct (a := a) χ _hχ hs f).mpr)

/-- Paper: Theorem 10.2.2.1, p. 446. At width zero the common-kernel and
dense-interpolant assertions hold for every nonnegative degree.
Deviation: Use the strict boundary cutoff. For degrees at most one the
theta image is dense and the admitted jet family is empty. -/
theorem spectralStripJet_zeroWidth_geometry (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (a s : ℝ) (hs : 0 ≤ s) :
    let J := SpectralStripJetIndex χ a 0 s
    let u : J → W'(-0, 0, s) := stripU(χ, le_rfl (a := (0 : ℝ)), hs)
    JetKernel(a, stripI(le_rfl (a := (0 : ℝ))), hs, u) ∧
      JetInterpolation(J, a, stripI(le_rfl (a := (0 : ℝ))), hs, u) := by
  let J := SpectralStripJetIndex χ a 0 s
  let claim (l : ℝ) (hl : l ≤ 0) := ∀ (hm : ∀ j : J, MemLp (stripJet(χ, j)) 2 L2μ'(l, 0, s)),
    let v (j : J) := (hm j).toLp (stripJet(χ, j))
    JetKernel(a, hl, hs, v) ∧ JetInterpolation(J, a, hl, hs, v)
  have H : claim 0 le_rfl := by
    intro hm v
    obtain ⟨e, he⟩ := spectralLineJet_zeroWidth_indices χ a s
    by_cases hs1 : 1 < s
    · have hv (i : SpectralLineJetIndex χ a s) : v (e i) = (lineU(χ, hs1)) i :=
        MemLp.toLp_congr _ _ (.of_forall (congrFun (he i)))
      have hK := spectralLineJet_commonKernel_direct (a := a) χ hχ hs1
      obtain ⟨f, hf, hcross, hd⟩ := spectralLineJet_denseInterpolants_direct (a := a) χ hχ hs1
      constructor
      · intro y
        constructor
        · intro hy j
          obtain ⟨i, rfl⟩ := e.surjective j
          rw [hv]
          exact (hK y).mp hy i
        · intro hy
          exact (hK y).mpr (fun i ↦ (hv i) ▸ hy (e i))
      · refine ⟨f ∘ e.symm, ?_, ?_, ?_⟩
        · intro j
          obtain ⟨i, rfl⟩ := e.surjective j
          simpa only [comp_apply, Equiv.symm_apply_apply, hv] using hf i
        · intro i j hij
          obtain ⟨k, rfl⟩ := e.surjective i
          obtain ⟨l, rfl⟩ := e.surjective j
          simpa only [comp_apply, Equiv.symm_apply_apply, hv] using hcross k l (fun h ↦ hij (congrArg e h))
        · let q := (Θ(a, le_rfl (a := (0 : ℝ)), hs)).mkQ
          change Dense (Submodule.span ℂ (range ((fun i ↦ q (f i)) ∘ e.symm)) : Set (spectralSobolevQuotient F a (le_rfl (a := (0 : ℝ))) hs))
          rwa [e.symm.surjective.range_comp]
    · have ht := globalThetaSobolev_line_eq_top_of_le_one (F := F) a s hs (le_of_not_gt hs1)
      have hemt (j : J) : False := by
        let i := e.symm j
        have hcut := ((lt_spectralBoundaryMultiplicity _ _ _).mp i.property).2
        linarith [Nat.cast_nonneg (α := ℝ) i.val.2.2]
      constructor
      · intro y
        rw [ht]
        exact ⟨fun _ j ↦ (hemt j).elim, fun _ ↦ Submodule.mem_top⟩
      · refine ⟨fun _ ↦ 0, fun j ↦ (hemt j).elim, fun i _ _ ↦ (hemt i).elim, ?_⟩
        intro q
        obtain ⟨f, rfl⟩ := (Θ(a, le_rfl (a := (0 : ℝ)), hs)).mkQ_surjective q
        apply subset_closure
        rw [(spectralSobolevQuotient_eq_zero a le_rfl hs f).mpr (ht ▸ Submodule.mem_top)]
        exact (Submodule.span ℂ _).zero_mem
  have transport (l : ℝ) (hl : l ≤ 0) (h0 : l = 0) : claim l hl := by
    subst l
    exact H
  exact transport (-0) _ neg_zero (spectralStripJet_memLp χ le_rfl hs)

/-- Paper: Theorem 10.2.1.1, pp. 440–443. The weighted theta closure is
the common kernel of the admitted line jets.
Gap: The line approximation required on p. 443 is the width-zero case of the strip common-kernel assertion. -/
theorem spectralLineJet_commonKernel (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let u : SpectralLineJetIndex χ a s → W'(0, 0, s) := lineU(χ, hs)
    JetKernel(a, le_rfl (a := (0 : ℝ)), lineHs(hs), u) := by
  apply spectralLineJet_zeroWidth_transport χ a hs
    (fun hl u ↦ JetKernel(a, hl, lineHs(hs), u))
  intro e y
  refine (spectralStripJet_commonKernel (a := a) χ _hχ (le_refl (0 : ℝ)) (lineHs(hs)) y).trans ?_
  exact e.surjective.forall

/-- Paper: Theorem 10.2.1.1, pp. 440–443. Single-jet interpolants have
representatives whose images span a dense subspace of the line quotient.
Gap: The interpolation and density asserted on p. 443 follow from the corresponding
strip assertion at width zero. -/
theorem spectralLineJet_denseInterpolants (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let J := SpectralLineJetIndex χ a s
    let u : J → W'(0, 0, s) := lineU(χ, hs)
    JetInterpolation(J, a, le_rfl (a := (0 : ℝ)), lineHs(hs), u) := by
  apply spectralLineJet_zeroWidth_transport χ a hs
    (fun hl u ↦ JetInterpolation(SpectralLineJetIndex χ a s, a, hl, lineHs(hs), u))
  intro e
  obtain ⟨v, hv, hc, hd⟩ :=
    spectralStripJet_denseInterpolants (a := a) χ _hχ (le_refl (0 : ℝ)) (lineHs(hs))
  refine ⟨v ∘ e, fun i ↦ hv (e i), fun i j hij ↦ hc (e i) (e j) (e.injective.ne hij), ?_⟩
  let q := (Θ(a, stripI(le_refl (0 : ℝ)), lineHs(hs))).mkQ
  change Dense (Submodule.span ℂ (range ((fun j ↦ q (v j)) ∘ e)) :
    Set (spectralSobolevQuotient F a (stripI(le_refl (0 : ℝ))) (lineHs(hs))))
  rwa [e.surjective.range_comp]

/-- Paper: Theorem 10.2.1.1 and Terminology 10.2.1.1, p. 440. The a-line
jets represent quotient functionals and admit a Markushevich biorthogonal family.
Deviation: Index directly by the admitted jets, so reindexing permits any
enumeration, including finite and empty families. Apply the strict cutoff. -/
theorem spectralLineMarkushevichBasis (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a s : ℝ} (hs : 1 < s) :
    let J := SpectralLineJetIndex χ a s
    let Q := spectralSobolevQuotient F a (le_rfl (a := (0 : ℝ))) (le_of_lt (zero_lt_one.trans hs))
    let D := spectralSobolevDualEmbedding F a (le_rfl (a := (0 : ℝ))) (le_of_lt (zero_lt_one.trans hs))
    Countable J ∧ ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j, D (Λ j) = (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j)) := by
  exact ⟨spectralLineJet_countable χ a s, spectralSobolevQuotient_basis_of_interpolation a
    (le_rfl (a := (0 : ℝ))) (lineHs(hs)) (lineU(χ, hs))
    (spectralLineJet_commonKernel χ hχ hs) (spectralLineJet_denseInterpolants χ hχ hs)⟩

/-- Paper: Corollary 10.2.1.4, p. 444. The a-line basis in the quotient dual
is normalized in the norm of its realization in the negative space.
Deviation: Apply the strict cutoff and allow finite or empty index types. -/
theorem spectralLineMarkushevichBasis_normalized
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ)
    {a s : ℝ} (hs : 1 < s) :
    let J := SpectralLineJetIndex χ a s
    let Q := spectralSobolevQuotient F a (le_rfl (a := (0 : ℝ))) (le_of_lt (zero_lt_one.trans hs))
    let D := spectralSobolevDualEmbedding F a (le_rfl (a := (0 : ℝ))) (le_of_lt (zero_lt_one.trans hs))
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      (∀ j, D (Λ j) = (spectralLineJet_memLp χ hs j).toLp (lineJet(χ, j))) ∧
      IsNormalizedSpectralFamily (fun j ↦ D (Λ j)) := by
  obtain ⟨x, Λ, hB, hD⟩ := (spectralLineMarkushevichBasis (a := a) χ _hχ hs).2
  obtain ⟨C, hC, hbound⟩ := spectralLineJet_annulus (a := a) χ _hχ hs
  refine ⟨x, Λ, hB, hD, ⟨C, ?_⟩, ⟨C⁻¹, inv_pos.mpr hC, ?_⟩⟩
  · intro j
    simpa only [hD j] using (hbound j).2
  · intro j
    simpa only [hD j] using (hbound j).1

/-- Paper: Theorem 10.2.2.1 and Terminology 10.2.2.1, p. 446. The strip
jets represent quotient functionals and admit a Markushevich biorthogonal family.
Deviation: Exclude the divergent endpoint and allow finite or empty enumerations. -/
theorem spectralStripMarkushevichBasis (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let J := SpectralStripJetIndex χ a α s
    let Q := spectralSobolevQuotient F a (neg_nonpos.mpr hα |>.trans hα) hs
    let D := spectralSobolevDualEmbedding F a (neg_nonpos.mpr hα |>.trans hα) hs
    Countable J ∧ ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j)) := by
  exact ⟨spectralStripJet_countable χ a α s, spectralSobolevQuotient_basis_of_interpolation a
    (stripI(hα)) hs (stripU(χ, hα, hs))
    (spectralStripJet_commonKernel χ hχ hα hs) (spectralStripJet_denseInterpolants χ hχ hα hs)⟩

private theorem spectralStripJet_norm_sq (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (j : SpectralStripJetIndex χ a α s)
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hν : ν = canonicalModulatedHaar m𝔽 hm𝔽) :
    ‖(spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))‖ ^ 2 =
      (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
        ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
          ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
  let u := (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))
  let f : ℝ → ℝ := fun x ↦
    Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹
  have h1 : ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(-α, α, s)) := spectralJet_lp_norm_sq u
  have h2 : ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(-α, α, s)) =
      ∫ g : C𝔽, Real.exp (2 * j.val.2.1 * logNorm g) * (logNorm g) ^ (2 * j.val.2.2.2)
        ∂(L2μ'(-α, α, s)) := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (spectralStripJet_memLp χ hα hs j)] with g hg
    rw [hg, spectralZeroJet_norm_sq]
  have h3 : ∫ g : C𝔽, Real.exp (2 * j.val.2.1 * logNorm g) * (logNorm g) ^ (2 * j.val.2.2.2)
      ∂(L2μ'(-α, α, s)) = ∫ g : C𝔽, f (logNorm g) ∂μ𝔽 := by
    rw [integral_withDensity_eq_integral_toReal_smul
      ((symmIntervalSobolevDensity_inv_continuous hα s).measurable.ennreal_ofReal)
      (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all μ𝔽 fun g ↦ ?_)
    dsimp only [f]
    rw [smul_eq_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (symmIntervalSobolevDensity_pos hα s (logNorm g)).le),
      mul_comm, stripJet_integrand_eq hα]
  have hmp : MeasurePreserving (fun g : C𝔽 ↦ logNorm g) ν volume := by
    rw [hν]
    exact sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have hlogm : AEMeasurable (fun g : C𝔽 ↦ logNorm g) ν :=
    (continuous_logModule' m𝔽).measurable.aemeasurable
  have hν_eq : ∫ g : C𝔽, f (logNorm g) ∂ν = ∫ x : ℝ, f x ∂volume := by
    rw [← hmp.map_eq,
      integral_map hlogm
        (stripJet_integrand_continuous α s j.val.2.1 j.val.2.2.2).aestronglyMeasurable]
  have h4 : ∫ g : C𝔽, f (logNorm g) ∂μ𝔽 = (Measure.haarScalarFactor μ𝔽 ν : ℝ) * ∫ x : ℝ, f x ∂volume := by
    conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, hν_eq]
  exact h1.trans (h2.trans (h3.trans h4))

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. A single
positive lower bound applies to the norms of all the strip jet classes.
Deviation: Use the strip zeros and reciprocal strip norm of Theorem 10.2.2.1.
Disjointness from the open ball also applies to the empty family. -/
theorem spectralStripJet_lowerBound (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    ∃ c : ℝ, 0 < c ∧ ∀ j : SpectralStripJetIndex χ a α s,
      let u := (spectralStripJet_memLp χ hα (le_of_lt (zero_lt_one.trans hs)) j).toLp (stripJet(χ, j))
      c ≤ ‖u‖ := by
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let hs₀ : 0 ≤ s := le_of_lt (zero_lt_one.trans hs)
  let c₀ : ℝ := Real.exp (-8 * α) * ((5 : ℝ) ^ (s / 2))⁻¹
  have hc₀ : 0 < c₀ := mul_pos (Real.exp_pos _) (inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _))
  have hfac_pos : 0 < (Measure.haarScalarFactor μ𝔽 ν : ℝ) := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν)
  let c : ℝ := Real.sqrt ((Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₀)
  refine ⟨c, Real.sqrt_pos.mpr (mul_pos hfac_pos hc₀), fun j ↦ ?_⟩
  dsimp only
  have hcond : (-α < j.val.2.1 ∧ j.val.2.1 < α) ∨
      ((j.val.2.1 = -α ∨ j.val.2.1 = α) ∧ 2 * (j.val.2.2.2 : ℝ) + 1 < s) := by
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with h1 h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2, ?_⟩
      have horder : (j.val.2.2.2 : ℝ) < (s - 1) / 2 :=
        ((lt_spectralBoundaryMultiplicity s _ _).mp hj).2
      linarith
    · omega
  have hf_int : Integrable (fun x : ℝ ↦
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹) volume :=
    spectralStripJet_integrable hα hs₀ hcond
  have hind_int : Integrable ((Icc (1 : ℝ) 2).indicator fun _ ↦ c₀) volume :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have hb : j.val.2.1 ∈ Icc (-α) α := (SpectralStripJetIndex.mem_strip_order_pos hα j).1
  have hle : ∀ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c₀) x ≤
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
    intro x
    by_cases hx : x ∈ Icc (1 : ℝ) 2
    · rw [indicator_of_mem hx]
      have hxpos : 0 ≤ x := by linarith [hx.1]
      have hexp : Real.exp (-8 * α) ≤ Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) := by
        rw [abs_of_nonneg hxpos]
        exact Real.exp_le_exp.mpr (by nlinarith [hb.1, hx.1, hx.2])
      have hpow : (1 : ℝ) ≤ x ^ (2 * j.val.2.2.2) := one_le_pow₀ hx.1
      have hbase : 1 + x ^ 2 ≤ 5 := by nlinarith [hx.1, hx.2]
      have hrpow : (1 + x ^ 2) ^ (s / 2) ≤ (5 : ℝ) ^ (s / 2) :=
        Real.rpow_le_rpow (by positivity) hbase (by linarith)
      have hinv : ((5 : ℝ) ^ (s / 2))⁻¹ ≤ ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) hrpow
      have hprod : Real.exp (-8 * α) ≤
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) := by
        calc
          Real.exp (-8 * α) = Real.exp (-8 * α) * 1 := (mul_one _).symm
          _ ≤ Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) :=
            mul_le_mul hexp hpow zero_le_one (Real.exp_pos _).le
      exact mul_le_mul hprod hinv
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by norm_num) _).le)
        (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
    · rw [indicator_of_notMem hx]
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
  have hint_le : c₀ ≤ ∫ x : ℝ,
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
    have h1 := integral_mono hind_int hf_int hle
    have h2 : ∫ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c₀) x ∂volume = c₀ := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc]
      norm_num
    linarith
  have hsq : (Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₀ ≤
      ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2 := by
    rw [spectralStripJet_norm_sq χ hα hs₀ j ν rfl]
    exact mul_le_mul_of_nonneg_left hint_le hfac_pos.le
  calc
    c = Real.sqrt ((Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₀) := rfl
    _ ≤ Real.sqrt (‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ :=
      Real.sqrt_sq (norm_nonneg _)

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
One integer bounds the multiplicity of every zero of every chosen completed Hecke
L-function: all components of the norm-one dual, all real parts and all ordinates at once.
This is the half of `spectralStripJet_order_and_margin_locally_finite_multiple_zeros` that
bounds the orders of the strip jets.
Reconstruction: The paper does not state this. It is the project's formulation of the bound on
the orders that the norm integral of Proposition 10.2.2.2, p. 447, needs, and it is not known
whether it is what the author intends.
Gap: The known bounds for the multiplicity of a zero grow with its height and with the
conductor. Over `ℚ` this statement contains a height-independent bound for the multiplicities
of the zeros of the Riemann zeta function, which is open, also on the Riemann hypothesis
(report on #7220). The statement that all zeros lie on the critical line does not supply it. -/
private theorem spectralStripJet_order_and_margin_multiplicity_bounded
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ) :
    ∃ M : ℕ, ∀ (ω : PontryaginDual C₁) (σ t : ℝ), multiplicity(χ ω, shift(σ, t)) ≤ M := by
  sorry

/-- Paper: Proposition 10.2.2.2, pp. 446–447. For one chosen Hecke character, each
multiple-zero line strictly to the right of the centre has a representative at bounded
height. The height bound may depend on the character.
Reconstruction: This isolates the single-character part of the strip margin.
Gap: Discreteness on compact rectangles does not control new abscissae at increasing heights. -/
private theorem spectralStripJet_multiple_zero_bounded_height_representatives
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ)
    (ω : PontryaginDual C₁) :
    ∃ T : ℝ, ∀ (σ t : ℝ), σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < multiplicity(χ ω, shift(σ, t)) →
      ∃ u : ℝ, |u| ≤ T ∧ 1 < multiplicity(χ ω, shift(σ, u)) := by
  sorry

/-- Paper: Proposition 10.2.2.2, pp. 446–447. For each choice of basepoints the real
interval (1/2, 1) contains only finitely many distinct multiple zeros of the family.
Reconstruction: This tests only ordinate zero. A different choice of basepoint may move
one prescribed ordinate to zero independently in each norm-one component.
Gap: Compactness gives finiteness for each character on this segment. Finiteness across
components for every choice of basepoints is open. -/
private theorem spectralStripJet_multiple_real_zeros_finite
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ) :
    {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω : PontryaginDual C₁,
      1 < multiplicity(χ ω, (σ : ℂ))}.Finite := by
  sorry

/-- For one character, a bounded height interval contributes only finitely many multiple-zero
abscissae in the closed right half of the critical strip. -/
theorem spectralStripJet_multiple_zero_lines_finite_on_compact
    (ψ : PontryaginDual C𝔽) (T : ℝ) :
    {σ : ℝ | σ ∈ Icc (1 / 2 : ℝ) 1 ∧ ∃ t : ℝ, |t| ≤ T ∧
      1 < multiplicity(ψ, shift(σ, t))}.Finite := by
  let R := (Icc (1 / 2 : ℝ) 1) ×ˢ (Icc (-T) T)
  let A (p : ℝ × ℝ) : ℂ := shift(p.1, p.2)
  have hA : Continuous A :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hK : IsCompact (A '' R) := (isCompact_Icc.prod isCompact_Icc).image hA
  let L := continuedCompletedHeckeL ψ
  have hL : MeromorphicOn L (A '' R) :=
    fun z _ ↦ (continuedCompletedHeckeL_spec ψ).1.meromorphicOn z (mem_univ z)
  apply (((MeromorphicOn.divisor L (A '' R)).finiteSupport hK).image Complex.re).subset
  rintro σ ⟨hσ, t, ht, hm⟩
  refine ⟨A (σ, t), ?_, by simp [A]⟩
  change MeromorphicOn.divisor L (A '' R) (A (σ, t)) ≠ 0
  rw [hL.divisor_apply ⟨(σ, t), ⟨hσ, abs_le.mp ht⟩, rfl⟩]
  change 1 < (meromorphicOrderAt L (A (σ, t))).untop₀.toNat at hm
  exact fun heq ↦ by rw [heq] at hm; simp at hm

/-- If two norm-twist charts differ by translation, their zero multiplicities agree
at the corresponding points. -/
private theorem spectralZeroMultiplicity_eq_of_chart_shift
    {ψ η : PontryaginDual C𝔽} {w : ℂ}
    (h : ideleClassNormTwist ψ 0 = ideleClassNormTwist η w) (z : ℂ) :
    multiplicity(ψ, z) = multiplicity(η, z + w) := by
  have hchart (s : ℂ) : ideleClassNormTwist ψ s = ideleClassNormTwist η (s + w) := by
    simpa only [zero_add, add_comm w s] using ideleClassNormTwist_add_of_eq h s
  have horder (f : adelePolarSubspace F) :
      meromorphicOrderAt (fun s ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist ψ s)) z =
        meromorphicOrderAt (fun s ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist η s))
          (z + w) := by
    simp_rw [hchart]
    exact meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (f := fun s ↦
      globalThetaMellinIntegral f.val (ideleClassNormTwist η s)) (c := w) (x := z)
  have hleast := isLeast_globalThetaMellinIntegral_orders ψ z
  simp_rw [horder] at hleast
  have he := hleast.unique (isLeast_globalThetaMellinIntegral_orders η (z + w))
  have hclip (o : WithTop ℤ) : (max 0 o).untop₀.toNat = o.untop₀.toNat := by
    cases o with
    | top => simp
    | coe n => simp only [← WithTop.coe_zero, ← WithTop.coe_max, WithTop.untop₀_coe]; omega
  exact (hclip _).symm.trans ((congrArg (fun o : WithTop ℤ ↦ o.untop₀.toNat) he).trans (hclip _))

/-- Paper: Notation 10.2.1.1, p. 440, and Proposition 10.2.2.2, pp. 446–447.
Relative to a prescribed section, each unitary lift has a unique real ordinate shift.
The shift identifies the quasi-characters and the zero multiplicities at every height
and real part, so differences of ordinates within this component are preserved. -/
theorem IsSpectralBasepointChoice.existsUnique_ordinate_shift
    {χ : PontryaginDual C₁ → PontryaginDual C𝔽} (hχ : IsSpectralBasepointChoice χ)
    (ψ : PontryaginDual C𝔽) :
    ∃! d : ℝ, ∀ σ t : ℝ,
      ideleClassNormTwist ψ (shift(σ, t)) =
        ideleClassNormTwist (χ (ψ.comp restriction)) (shift(σ, t + d)) ∧
      multiplicity(ψ, shift(σ, t)) = multiplicity(χ (ψ.comp restriction), shift(σ, t + d)) := by
  let ω := ψ.comp restriction
  have hres (g : C₁) : ideleClassNormTwist ψ 0 g.val = (ω g : ℂ) := by
    change (ψ g.val : ℂ) * _ ^ (0 : ℂ) = ψ g.val
    simp
  obtain ⟨w, hw, huniq⟩ := hχ.existsUnique_normTwist ω (ideleClassNormTwist ψ 0) hres
  have hre : w.re = 0 := by
    have he := congrArg (quasiCharacterAbscissa (ideleClassNorm F)
      (isProperMap_ideleClassNorm F) ideleClassNorm_ne_one) hw
    simpa only [quasiCharacterAbscissa_ideleClassNormTwist, Complex.zero_re] using he.symm
  have hwI : (w.im : ℂ) * Complex.I = w := by simpa [hre] using Complex.re_add_im w
  have hshift (σ t : ℝ) : shift(σ, t + w.im) = shift(σ, t) + w := by
    calc
      _ = shift(σ, t) + (w.im : ℂ) * Complex.I := by ring
      _ = _ := by rw [hwI]
  refine ⟨w.im, fun σ t ↦ ?_, fun d hd ↦ ?_⟩
  · rw [hshift]
    refine ⟨?_, spectralZeroMultiplicity_eq_of_chart_shift hw _⟩
    simpa only [zero_add, add_comm w] using ideleClassNormTwist_add_of_eq hw (shift(σ, t))
  · have he : ideleClassNormTwist ψ 0 = ideleClassNormTwist (χ ω) ((d : ℂ) * Complex.I) := by
      simpa using (hd 0 0).1
    have hu := congrArg Complex.im (huniq _ he)
    simpa using hu

/-- Paper: Notation 10.2.1.1, p. 440, and Proposition 10.2.2.2, pp. 446–447.
Two unitary lifts with the same norm-one restriction have the same zero multiplicities
after one unique vertical translation of their norm charts. -/
theorem spectralZeroMultiplicity_existsUnique_shift_of_restriction_eq
    (ψ η : PontryaginDual C𝔽) (hres : ψ.comp restriction = η.comp restriction) :
    ∃! d : ℝ, ∀ σ t : ℝ,
      ideleClassNormTwist ψ (shift(σ, t)) = ideleClassNormTwist η (shift(σ, t + d)) ∧
      multiplicity(ψ, shift(σ, t)) = multiplicity(η, shift(σ, t + d)) := by
  classical
  obtain ⟨χ₀, hχ₀⟩ := exists_spectralBasepointChoice F
  let χ := Function.update χ₀ (ψ.comp restriction) η
  have hη : χ (ψ.comp restriction) = η := Function.update_self ..
  have hχ : IsSpectralBasepointChoice χ := by
    intro ω
    by_cases hω : ω = ψ.comp restriction
    · subst ω
      rw [hη]
      exact hres.symm
    · rw [show χ ω = χ₀ ω from Function.update_of_ne hω ..]
      exact hχ₀ ω
  simpa only [hη] using hχ.existsUnique_ordinate_shift ψ

/-- Translating a unitary norm chart to ordinate zero preserves its norm-one component and
all completed Hecke zero multiplicities. -/
private theorem spectralStripJet_recenter (ψ : PontryaginDual C𝔽) (t : ℝ) :
    ∃ θ : PontryaginDual C𝔽, θ.comp restriction = ψ.comp restriction ∧ ∀ σ : ℝ,
      multiplicity(θ, (σ : ℂ)) = multiplicity(ψ, shift(σ, t)) := by
  let a := (t : ℂ) * Complex.I
  let c := ideleClassNormTwist ψ a
  have hn (g : C𝔽) : ‖c g‖ = 1 := by
    change ‖(ψ g : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ a)‖ = 1
    rw [norm_mul, Circle.norm_coe, Complex.norm_cpow_eq_rpow_re_of_pos
      (NNReal.coe_pos.mpr (Units.zero_lt _))]
    simp [a]
  let θ : PontryaginDual C𝔽 :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hn g)⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun x y ↦ Subtype.ext (map_mul c x y)
      continuous_toFun := c.continuous.subtype_mk _ }
  have hθ : ideleClassNormTwist θ 0 = ideleClassNormTwist ψ a := by
    ext1 g
    change c g * _ ^ (0 : ℂ) = c g
    simp
  refine ⟨θ, ?_, fun σ ↦ spectralZeroMultiplicity_eq_of_chart_shift hθ (σ : ℂ)⟩
  ext g : 1
  apply Subtype.ext
  change (ψ g.val : ℂ) * ((((ideleClassNorm F g.val).val : ℝ) : ℂ) ^ a) = ψ g.val
  rw [show ideleClassNorm F g.val = 1 from g.property]
  simp

/-- Paper: Proposition 10.2.2.2, pp. 446–447. Finiteness of the multiple real zeros
for every choice of basepoints is equivalent to a finite cover of all the multiple zeros
in the open right half of the critical strip. There are finitely many exceptional
norm-one characters and finitely many real parts. At any height, a multiple zero of
any unitary Hecke character either belongs to an exceptional component or has one of
these real parts. The same two finite sets work for every choice of basepoints.
Reconstruction: This characterizes the real-segment part of the strip margin. -/
theorem spectralStripJet_multiple_real_zeros_finite_iff_finite_cover :
    (∀ (χ : PontryaginDual C₁ → PontryaginDual C𝔽), IsSpectralBasepointChoice χ →
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω : PontryaginDual C₁,
        1 < multiplicity(χ ω, (σ : ℂ))}.Finite) ↔
    ∃ (E : Finset (PontryaginDual C₁)) (S : Finset ℝ), ∀ (ψ : PontryaginDual C𝔽) (σ t : ℝ),
      σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < multiplicity(ψ, shift(σ, t)) →
        ψ.comp restriction ∈ E ∨ σ ∈ S := by
  classical
  constructor
  · intro hreal
    by_contra! hcover
    -- Greedily take zeros in fresh components and at fresh real parts, moving each to height zero.
    let component (p : PontryaginDual C𝔽 × ℝ) := p.1.comp restriction
    let P (p : PontryaginDual C𝔽 × ℝ) :=
      p.2 ∈ Ioo (1 / 2 : ℝ) 1 ∧ 1 < multiplicity(p.1, (p.2 : ℂ))
    let r (p q : PontryaginDual C𝔽 × ℝ) := component p ≠ component q ∧ p.2 ≠ q.2
    have : Std.Symm r := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
    obtain ⟨p, hp, hpair⟩ := exists_seq_of_forall_finset_exists' P r (fun K _ ↦ by
      obtain ⟨ψ, σ, t, hσ, hm, hψ, hs⟩ := hcover (K.image component) (K.image Prod.snd)
      obtain ⟨θ, hθ, hmove⟩ := spectralStripJet_recenter ψ t
      have hmθ : 1 < multiplicity(θ, (σ : ℂ)) := by rwa [hmove]
      refine ⟨(θ, σ), ⟨hσ, hmθ⟩, fun q hq ↦ ⟨?_, ?_⟩⟩
      · exact fun he ↦ hψ (Finset.mem_image.mpr ⟨q, hq, he.trans hθ⟩)
      · exact fun he ↦ hs (Finset.mem_image.mpr ⟨q, hq, he⟩))
    have hcomp : Injective (fun n ↦ component (p n)) :=
      injective_iff_pairwise_ne.mpr fun _ _ h ↦ (hpair h).1
    have hparts : Injective (fun n ↦ (p n).2) :=
      injective_iff_pairwise_ne.mpr fun _ _ h ↦ (hpair h).2
    -- The components are distinct, so the selected characters extend to one choice of basepoints.
    obtain ⟨χ₀, hχ₀⟩ := exists_spectralBasepointChoice F
    let χ := extend (fun n ↦ component (p n)) (fun n ↦ (p n).1) χ₀
    have hmatch (n : ℕ) : χ (component (p n)) = (p n).1 := hcomp.extend_apply _ _ n
    have hχ : IsSpectralBasepointChoice χ := by
      intro ω
      by_cases h : ∃ n, component (p n) = ω
      · obtain ⟨n, rfl⟩ := h
        rw [hmatch]
      · exact (congrArg (fun ψ : PontryaginDual C𝔽 ↦ ψ.comp restriction)
          (extend_apply' _ χ₀ ω h)).trans (hχ₀ ω)
    apply infinite_range_of_injective hparts
    apply (hreal χ hχ).subset
    rintro _ ⟨n, rfl⟩
    refine ⟨(hp n).1, component (p n), ?_⟩
    rw [hmatch]
    exact (hp n).2
  · rintro ⟨E, S, hcover⟩ χ hχ
    let Z (ω : PontryaginDual C₁) :=
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ 1 < multiplicity(χ ω, (σ : ℂ))}
    have hZ (ω : PontryaginDual C₁) : (Z ω).Finite := by
      apply (spectralStripJet_multiple_zero_lines_finite_on_compact (χ ω) 0).subset
      rintro σ ⟨hσ, hm⟩
      exact ⟨⟨hσ.1.le, hσ.2.le⟩, 0, by simp, by simpa using hm⟩
    apply (S.finite_toSet.union (E.finite_toSet.biUnion fun ω _ ↦ hZ ω)).subset
    rintro σ ⟨hσ, ω, hm⟩
    rcases hcover (χ ω) σ 0 hσ (by simpa using hm) with hω | hs
    · rw [hχ ω] at hω
      exact Or.inr (mem_iUnion₂.mpr ⟨ω, hω, hσ, hm⟩)
    · exact Or.inl hs

/-- Reflect a multiple zero into the opposite half of the strip by the completed functional
equation. Reflection negates the ordinate and replaces the character by its inverse. -/
private theorem spectralStripJet_multiple_zero_reflect (ψ : PontryaginDual C𝔽) (σ t : ℝ) :
    multiplicity(ψ, shift(σ, t)) = multiplicity(ψ⁻¹, shift(1 - σ, (-t : ℝ))) := by
  obtain ⟨ε, hε, hne, he⟩ := completedHeckeL_continuation_functionalEquation ψ _ _
    (continuedCompletedHeckeL_spec ψ).1 (continuedCompletedHeckeL_spec ψ).2
    (continuedCompletedHeckeL_spec ψ⁻¹).1 (continuedCompletedHeckeL_spec ψ⁻¹).2
  let r (z : ℂ) := 1 - z
  have heq : continuedCompletedHeckeL ψ⁻¹ ∘ r = ε * continuedCompletedHeckeL ψ := funext he
  have hr : HasDerivAt r (-1) (shift(σ, t)) := (hasDerivAt_id _).const_sub 1
  have ho := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL ψ⁻¹)
    (show AnalyticAt ℂ r (shift(σ, t)) by dsimp [r]; fun_prop) (hr.deriv.trans_ne (by norm_num))
  rw [heq, meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt _) (hne _)] at ho
  have hz : r (shift(σ, t)) = shift(1 - σ, (-t : ℝ)) := by
    dsimp [r]
    push_cast
    ring
  rw [hz] at ho
  rw [ho]

/-- A multiple zero with real part greater than one half lies in the open critical strip. -/
private theorem spectralStripJet_multiple_zero_re_lt_one (ψ : PontryaginDual C𝔽)
    {σ t : ℝ} (hσ : 1 / 2 < σ) (h : 1 < multiplicity(ψ, shift(σ, t))) : σ < 1 := by
  have hp : 0 < vanishingOrder(ψ, shift(σ, t)) := by
    generalize vanishingOrder(ψ, shift(σ, t)) = o at *
    cases o with
    | top => simp at h
    | coe k =>
      rw [WithTop.untop₀_coe] at h
      exact_mod_cast (by omega : 0 < k)
  simpa using completedHeckeL_continuation_zeros ψ _ (continuedCompletedHeckeL_spec ψ).1
    (continuedCompletedHeckeL_spec ψ).2 (by simpa using (show 0 < σ by linarith)) hp

/-- Choose a witness component for each abscissa, then one abscissa representing each
component so chosen. A single choice of ordinates sees all the representatives. -/
private theorem spectralStripJet_multiple_zero_finite_of_slices
    (R : PontryaginDual C₁ → ℝ → ℝ → Prop)
    (hfixed : ∀ ω, {σ | ∃ t, R ω σ t}.Finite)
    (hslice : ∀ τ : PontryaginDual C₁ → ℝ, {σ | ∃ ω, R ω σ (τ ω)}.Finite) :
    {σ | ∃ ω t, R ω σ t}.Finite := by
  classical
  let S := {σ | ∃ ω t, R ω σ t}
  choose component ordinate hw using fun σ : S ↦ σ.property
  choose rep hrep using fun ω : range component ↦ ω.property
  let τ (ω : PontryaginDual C₁) := if h : ω ∈ range component then ordinate (rep ⟨ω, h⟩) else 0
  have hselected : (range (fun ω ↦ (rep ω : ℝ))).Finite := (hslice τ).subset <| by
    rintro _ ⟨ω, rfl⟩
    exact ⟨ω, by simpa only [τ, dite_eq_left ω.property, hrep] using hw (rep ω)⟩
  have hinj : Injective (fun ω ↦ (rep ω : ℝ)) := fun i j h ↦
    Subtype.ext <| (hrep i).symm.trans ((congrArg component (Subtype.ext h)).trans (hrep j))
  have hfin : (range component).Finite := finite_coe_iff.mp ((finite_range_iff hinj).mp hselected)
  apply (hfin.biUnion fun ω _ ↦ hfixed ω).subset
  intro σ hσ
  let p : S := ⟨σ, hσ⟩
  exact mem_iUnion₂.mpr ⟨component p, mem_range_self p, ordinate p, hw p⟩

/-- The finite-line assertion for every section is equivalent to two tests in the open
right half of the strip. One tests each component separately over unbounded heights.
The other uses a single real segment for all components, allowing every choice of section. -/
private theorem spectralStripJet_multiple_zero_lines_iff :
    (∀ (χ : PontryaginDual C₁ → PontryaginDual C𝔽), IsSpectralBasepointChoice χ →
      {σ : ℝ | ∃ (ω : PontryaginDual C₁) (t : ℝ), 1 < multiplicity(χ ω, shift(σ, t))}.Finite) ↔
    (∀ (χ : PontryaginDual C₁ → PontryaginDual C𝔽), IsSpectralBasepointChoice χ →
      ∀ ω : PontryaginDual C₁, ∃ T : ℝ, ∀ (σ t : ℝ), σ ∈ Ioo (1 / 2 : ℝ) 1 →
      1 < multiplicity(χ ω, shift(σ, t)) → ∃ u : ℝ, |u| ≤ T ∧
        1 < multiplicity(χ ω, shift(σ, u))) ∧
    (∀ (χ : PontryaginDual C₁ → PontryaginDual C𝔽), IsSpectralBasepointChoice χ →
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω : PontryaginDual C₁,
        1 < multiplicity(χ ω, (σ : ℂ))}.Finite) := by
  constructor
  · intro h
    constructor
    · intro χ hχ ω
      let S := {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ t : ℝ, 1 < multiplicity(χ ω, shift(σ, t))}
      have hS : S.Finite := (h χ hχ).subset fun σ hσ ↦ by
        obtain ⟨t, ht⟩ := hσ.2
        exact ⟨ω, t, ht⟩
      choose u hu using fun σ : S ↦ σ.property.2
      let := hS.fintype
      obtain ⟨T, hT⟩ := (finite_range (fun σ : S ↦ |u σ|)).bddAbove
      refine ⟨T, fun σ t hs hm ↦ ?_⟩
      let p : S := ⟨σ, hs, t, hm⟩
      exact ⟨u p, hT (mem_range_self p), hu p⟩
    · intro χ hχ
      apply (h χ hχ).subset
      rintro σ ⟨_, ω, hm⟩
      exact ⟨ω, 0, by simpa using hm⟩
  · rintro ⟨hfixed, hreal⟩ χ hχ
    let right (η : PontryaginDual C₁ → PontryaginDual C𝔽) :=
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ (ω : PontryaginDual C₁) (t : ℝ),
        1 < multiplicity(η ω, shift(σ, t))}
    have hright (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) :
        (right χ).Finite := by
      let R (ω : PontryaginDual C₁) (σ t : ℝ) :=
        σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ 1 < multiplicity(χ ω, shift(σ, t))
      have hsingle (ω : PontryaginDual C₁) : {σ | ∃ t, R ω σ t}.Finite := by
        obtain ⟨T, hT⟩ := hfixed χ hχ ω
        apply (spectralStripJet_multiple_zero_lines_finite_on_compact (χ ω) T).subset
        rintro σ ⟨t, hs, hm⟩
        exact ⟨⟨hs.1.le, hs.2.le⟩, hT σ t hs hm⟩
      have hslice (τ : PontryaginDual C₁ → ℝ) : {σ | ∃ ω, R ω σ (τ ω)}.Finite := by
        choose η hres hmove using fun ω ↦ spectralStripJet_recenter (χ ω) (τ ω)
        have hη : IsSpectralBasepointChoice η := fun ω ↦ (hres ω).trans (hχ ω)
        apply (hreal η hη).subset
        rintro σ ⟨ω, hs, hm⟩
        refine ⟨hs, ω, ?_⟩
        rw [hmove ω σ]
        exact hm
      apply (spectralStripJet_multiple_zero_finite_of_slices R hsingle hslice).subset
      rintro σ ⟨hs, ω, t, hm⟩
      exact ⟨ω, t, hs, hm⟩
    let dual (ω : PontryaginDual C₁) := (χ ω⁻¹)⁻¹
    have hdual : IsSpectralBasepointChoice dual := by
      intro ω
      ext g : 1
      have hg := DFunLike.congr_fun (hχ (ω⁻¹)) g
      change ((χ ω⁻¹) g.val)⁻¹ = ω g
      change (χ ω⁻¹) g.val = (ω g)⁻¹ at hg
      simp [hg]
    have hr : (right χ).Finite := hright χ hχ
    have hd : (right dual).Finite := hright dual hdual
    apply ((hr.union (hd.image (fun σ : ℝ ↦ 1 - σ))).insert (1 / 2)).subset
    rintro σ ⟨ω, t, h⟩
    rcases lt_trichotomy σ (1 / 2) with hl | hc | hr
    · apply Or.inr
      apply Or.inr
      have hz : 1 < multiplicity((χ ω)⁻¹, shift(1 - σ, (-t : ℝ))) := by
        rwa [← spectralStripJet_multiple_zero_reflect]
      have half : 1 / 2 < 1 - σ := by linarith
      refine ⟨1 - σ, ⟨⟨half, spectralStripJet_multiple_zero_re_lt_one (χ ω)⁻¹ (t := -t) half hz⟩, ω⁻¹, -t, ?_⟩,
        by ring⟩
      simpa [dual] using hz
    · exact Or.inl hc
    · exact Or.inr (Or.inl ⟨⟨hr, spectralStripJet_multiple_zero_re_lt_one (χ ω) (t := t) hr h⟩, ω, t, h⟩)

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
The multiple zeros of the chosen completed Hecke L-functions lie on finitely many vertical
lines, over all components of the norm-one dual and all ordinates.
This is the half of `spectralStripJet_order_and_margin_locally_finite_multiple_zeros` that
keeps the jets of high order away from the edges of a strip.
Reconstruction: The paper does not state this. It is the project's formulation of the margin
that the norm integral of Proposition 10.2.2.2, p. 447, needs, and it is not known whether it
is what the author intends.
It is reduced below to bounded-height representatives for each character and finiteness on
the real segment for every choice of basepoints. Both inputs remain open.
The statement follows from the paper's main claim, that all zeros in
the critical strip have real part `1/2`, but Proposition 10.2.2.2 stands on the way to that
claim. For the splitting field of `X³ - 2` it already gives a zero-free strip to the left of
the line of real part `1` for an Artin L-function (report on #7220). -/
private theorem spectralStripJet_order_and_margin_multiple_zero_lines_finite
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ) :
    {σ : ℝ | ∃ (ω : PontryaginDual C₁) (t : ℝ),
      1 < multiplicity(χ ω, shift(σ, t))}.Finite := by
  exact (spectralStripJet_multiple_zero_lines_iff (F := F)).2
    ⟨spectralStripJet_multiple_zero_bounded_height_representatives,
      spectralStripJet_multiple_real_zeros_finite⟩ χ _hχ

/-- Near any real number there are only finitely many distinct pairs of real part and
multiplicity among multiple completed Hecke zeros, over all ordinates and chosen characters.
The norm integral on p. 447 gives no such restriction. It would suffice to bound the
multiplicities on the line with that real part and exclude multiple zeros on all other
sufficiently nearby vertical lines.
Reconstruction: The paper does not state this. It is the project's formulation of what the
estimates of Remark 10.2.1.5 and Proposition 10.2.2.2 need, and it is not known whether it is
what the author intends.
Proved here (#7425) from two open statements, which are its two halves in their global form:
`spectralStripJet_order_and_margin_multiplicity_bounded` and
`spectralStripJet_order_and_margin_multiple_zero_lines_finite`. Neither a bound for the
multiplicities of the zeros on a vertical line nor the absence of multiple zeros on the nearby
lines is known, and Remark 10.2.1.5 and Proposition 10.2.2.2 supply no argument for either. -/
private theorem spectralStripJet_order_and_margin_locally_finite_multiple_zeros
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ) (x : ℝ) :
    ∃ U ∈ 𝓝 x, {p : ℝ × ℕ | p.1 ∈ U ∧ 1 < p.2 ∧ ∃ (ω : PontryaginDual C₁) (t : ℝ),
      multiplicity(χ ω, shift(p.1, t)) = p.2}.Finite := by
  obtain ⟨M, hM⟩ := spectralStripJet_order_and_margin_multiplicity_bounded χ _hχ
  refine ⟨univ, univ_mem, ?_⟩
  refine ((spectralStripJet_order_and_margin_multiple_zero_lines_finite χ _hχ).prod
    (finite_Iic M)).subset ?_
  rintro ⟨σ, n⟩ ⟨-, hn, ω, t, h⟩
  exact ⟨⟨ω, t, h.symm ▸ hn⟩, h ▸ hM ω σ t⟩

/-- Paper: Proposition 10.2.2.2, pp. 446–447. A uniform strip estimate requires a
bound on admitted jet orders and a boundary margin for the nonintegrable powers.
Gap: The paper supplies neither estimate for the actual completed Hecke divisor. -/
theorem spectralStripJet_order_and_margin (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (_hα : 0 ≤ α) (_hs : 1 < s) :
    ∃ (K : ℕ) (δ : ℝ), 0 < δ ∧ ∀ j : SpectralStripJetIndex χ a α s,
      j.val.2.2.2 ≤ K ∧ ((s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → |j.val.2.1| ≤ α - δ) := by
  let S := {p : ℝ × ℕ | |p.1 - a| < α ∧ 1 < p.2 ∧ ∃ (ω : PontryaginDual C₁) (t : ℝ),
    multiplicity(χ ω, shift(p.1, t)) = p.2}
  -- Compactness turns the local arithmetic input into a finite set for this strip.
  have hfin : S.Finite := by
    choose U hU hloc using spectralStripJet_order_and_margin_locally_finite_multiple_zeros χ _hχ
    obtain ⟨T, _, hcover⟩ := (isCompact_Icc (a := a - α) (b := a + α)).elim_nhds_subcover
      U (fun x _ ↦ hU x)
    apply (T.finite_toSet.biUnion fun x _ ↦ hloc x).subset
    intro p hp
    obtain ⟨hl, hr⟩ := abs_lt.mp hp.1
    have hx : p.1 ∈ Icc (a - α) (a + α) := ⟨by linarith, by linarith⟩
    obtain ⟨x, hxT, hxU⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion₂.mpr ⟨x, hxT, hxU, hp.2⟩
  obtain ⟨K, hK⟩ := (hfin.image Prod.snd).bddAbove
  -- Adjoining 1 supplies a positive margin also when the open strip has no multiple zeros.
  let d (p : ℝ × ℕ) := α - |p.1 - a|
  obtain ⟨δ, hmem, hmin⟩ := Set.exists_min_image _ id ((hfin.image d).insert 1)
    (insert_nonempty _ _)
  have hδ : 0 < δ := by
    rcases hmem with rfl | ⟨p, hp, rfl⟩
    · exact one_pos
    · exact sub_pos.mpr hp.1
  refine ⟨max K ⌈(s - 1) / 2⌉₊, δ, hδ, fun j ↦ ?_⟩
  by_cases hlow : (j.val.2.2.2 : ℝ) < (s - 1) / 2
  · exact ⟨(Nat.lt_ceil.mpr hlow).le.trans (le_max_right _ _), fun h ↦ (hlow.not_ge h).elim⟩
  have hk : 0 < j.val.2.2.2 := by exact_mod_cast (by linarith : (0 : ℝ) < j.val.2.2.2)
  have hj := j.property
  unfold spectralStripMultiplicity at hj
  split_ifs at hj with hb he
  · let N := multiplicity(χ j.val.1, shift(a + j.val.2.1, j.val.2.2.1))
    have hN : j.val.2.2.2 < N := hj
    let p : ℝ × ℕ := (a + j.val.2.1, N)
    have hp : p ∈ S :=
      ⟨by simpa [p] using abs_lt.mpr hb, show 1 < N by omega,
        j.val.1, j.val.2.2.1, rfl⟩
    have horder : N ≤ K := hK (mem_image_of_mem Prod.snd hp)
    have hdist : δ ≤ α - |j.val.2.1| := by
      simpa [d, p] using hmin (d p) (Or.inr (mem_image_of_mem d hp))
    exact ⟨hN.le.trans (horder.trans (le_max_left _ _)), fun _ ↦ by linarith⟩
  · exact (hlow ((lt_spectralBoundaryMultiplicity _ _ _).mp hj).2).elim
  · omega

/-- Paper: Proposition 10.2.2.2, pp. 446–447. Finitely many integrable
boundary powers and a positive exponential margin on all other powers give
a uniform norm bound. -/
theorem spectralStripJet_upperBound_of_margin (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (K : ℕ) (δ : ℝ) (_hδ : 0 < δ)
    (_h : ∀ j : SpectralStripJetIndex χ a α s, j.val.2.2.2 ≤ K ∧
      ((s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → |j.val.2.1| ≤ α - δ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : SpectralStripJetIndex χ a α s,
      ‖(spectralStripJet_memLp χ hα (lineHs(hs)) j).toLp (stripJet(χ, j))‖ ≤ C := by
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let hs₀ : 0 ≤ s := lineHs(hs)
  let N : ℕ := Nat.ceil ((s - 1) / 2)
  let M_bdry : ℝ := ∑ m ∈ Finset.range N,
    ∫ x : ℝ, x ^ (2 * m) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume
  let M_int : ℝ :=
    ∫ x : ℝ, Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K)) ∂volume
  have hfac_nonneg : 0 ≤ (Measure.haarScalarFactor μ𝔽 ν : ℝ) := NNReal.coe_nonneg _
  have hM_bdry_nonneg : 0 ≤ M_bdry :=
    Finset.sum_nonneg fun m _ ↦ integral_nonneg fun x ↦
      mul_nonneg (Even.pow_nonneg (even_two_mul m) x)
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
  have hM_int_nonneg : 0 ≤ M_int :=
    integral_nonneg fun x ↦
      mul_nonneg (Real.exp_pos _).le (add_nonneg zero_le_one (Even.pow_nonneg (even_two_mul K) x))
  have hM_int_integrable : Integrable (fun x : ℝ ↦ Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K)))
      volume := by
    have h0 := integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * δ) 0
    have hK := integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * δ) K
    refine (h0.add hK).congr (ae_of_all _ fun x ↦ ?_)
    change Real.exp (-(2 * δ) * |x|) * x ^ (2 * 0) +
        Real.exp (-(2 * δ) * |x|) * x ^ (2 * K) =
      Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K))
    simp only [mul_zero, pow_zero, mul_one]
    ring
  let B : ℝ := 1 + (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (M_bdry + M_int)
  have hB_pos : 0 < B := by
    have : 0 ≤ (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (M_bdry + M_int) :=
      mul_nonneg hfac_nonneg (add_nonneg hM_bdry_nonneg hM_int_nonneg)
    linarith
  refine ⟨Real.sqrt B, Real.sqrt_pos.mpr hB_pos, fun j ↦ ?_⟩
  have hcond : (-α < j.val.2.1 ∧ j.val.2.1 < α) ∨
      ((j.val.2.1 = -α ∨ j.val.2.1 = α) ∧ 2 * (j.val.2.2.2 : ℝ) + 1 < s) := by
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with h1 h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2, ?_⟩
      have horder : (j.val.2.2.2 : ℝ) < (s - 1) / 2 :=
        ((lt_spectralBoundaryMultiplicity s _ _).mp hj).2
      linarith
    · omega
  have hf_int : Integrable (fun x : ℝ ↦
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹) volume :=
    spectralStripJet_integrable hα hs₀ hcond
  have hint_bound : ∫ x : ℝ,
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_bdry + M_int := by
    by_cases hk : (j.val.2.2.2 : ℝ) < (s - 1) / 2
    · have hk' : 2 * (j.val.2.2.2 : ℝ) + 1 < s := by linarith
      have hb : j.val.2.1 ∈ Icc (-α) α := (SpectralStripJetIndex.mem_strip_order_pos hα j).1
      have hba : |j.val.2.1| ≤ α := abs_le.mpr hb
      have h1 : ∫ x : ℝ,
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
            ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤
          ∫ x : ℝ, x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
        refine integral_mono hf_int (integrable_pow_mul_rpow_inv hk') fun x ↦ ?_
        have hbx : j.val.2.1 * x ≤ α * |x| := by
          calc
            j.val.2.1 * x ≤ |j.val.2.1 * x| := le_abs_self _
            _ = |j.val.2.1| * |x| := abs_mul _ _
            _ ≤ α * |x| := mul_le_mul_of_nonneg_right hba (abs_nonneg x)
        have hexp : Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by linarith)
        rw [mul_assoc]
        calc
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) *
              (x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹)
            ≤ 1 * (x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
              mul_le_mul_of_nonneg_right hexp
                (mul_nonneg (Even.pow_nonneg (even_two_mul _) x)
                  (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le))
          _ = x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := one_mul _
      have hjN : j.val.2.2.2 ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_ceil.mpr hk)
      have h2 : ∫ x : ℝ, x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_bdry :=
        Finset.single_le_sum
          (f := fun m ↦ ∫ x : ℝ, x ^ (2 * m) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume)
          (fun m _ ↦ integral_nonneg fun x ↦
            mul_nonneg (Even.pow_nonneg (even_two_mul m) x)
              (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _))) hjN
      linarith
    · have hk_ge : (s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) := not_lt.mp hk
      have hmargin : |j.val.2.1| ≤ α - δ := (_h j).2 hk_ge
      have hkK : j.val.2.2.2 ≤ K := (_h j).1
      have h1 : ∫ x : ℝ,
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
            ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_int := by
        refine integral_mono hf_int hM_int_integrable fun x ↦ ?_
        have hbx : j.val.2.1 * x ≤ (α - δ) * |x| := by
          calc
            j.val.2.1 * x ≤ |j.val.2.1 * x| := le_abs_self _
            _ = |j.val.2.1| * |x| := abs_mul _ _
            _ ≤ (α - δ) * |x| := mul_le_mul_of_nonneg_right hmargin (abs_nonneg x)
        have hexp : Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) ≤ Real.exp (-(2 * δ) * |x|) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have hpow : x ^ (2 * j.val.2.2.2) ≤ 1 + x ^ (2 * K) := by
          have hxa : x ^ (2 * j.val.2.2.2) = |x| ^ (2 * j.val.2.2.2) := by
            rw [pow_mul, ← sq_abs, ← pow_mul]
          have hxaK : x ^ (2 * K) = |x| ^ (2 * K) := by
            rw [pow_mul, ← sq_abs, ← pow_mul]
          rw [hxa, hxaK]
          rcases le_total |x| 1 with hx1 | hx1
          · have : |x| ^ (2 * j.val.2.2.2) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
            linarith [pow_nonneg (abs_nonneg x) (2 * K)]
          · have : |x| ^ (2 * j.val.2.2.2) ≤ |x| ^ (2 * K) :=
              pow_le_pow_right₀ hx1 (Nat.mul_le_mul_left 2 hkK)
            linarith
        have hinv_le : ((1 + x ^ 2) ^ (s / 2))⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith))
        calc
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
              ((1 + x ^ 2) ^ (s / 2))⁻¹
            ≤ Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) * 1 :=
              mul_le_mul_of_nonneg_left hinv_le
                (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
          _ = Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) := mul_one _
          _ ≤ Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K)) :=
              mul_le_mul hexp hpow (Even.pow_nonneg (even_two_mul _) x) (Real.exp_pos _).le
      linarith
  have hsq : ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2 ≤ B := by
    rw [spectralStripJet_norm_sq χ hα hs₀ j ν rfl]
    have hmul : (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
        ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
          ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤
        (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (M_bdry + M_int) :=
      mul_le_mul_of_nonneg_left hint_bound hfac_nonneg
    dsimp only [B]
    linarith
  calc
    ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖
      = Real.sqrt (‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hsq

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. A single upper
bound applies to the norms of all the strip jet classes.
Deviation: Use the strip zeros and both cutoff equations of Theorem 10.2.2.1,
with the reciprocal strip norm throughout. -/
theorem spectralStripJet_upperBound (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : SpectralStripJetIndex χ a α s,
      let u := (spectralStripJet_memLp χ hα (le_of_lt (zero_lt_one.trans hs)) j).toLp (stripJet(χ, j))
      ‖u‖ ≤ C := by
  obtain ⟨K, δ, hδ, h⟩ := spectralStripJet_order_and_margin (a := a) χ _hχ hα hs
  exact spectralStripJet_upperBound_of_margin χ hα hs K δ hδ h

/-- Paper: Corollary 10.2.2.3, p. 447. The strip basis in the quotient dual
is normalized in the norm of its realization in the reciprocal strip space.
Deviation: Use the strip zeros and cutoff of Theorem 10.2.2.1. The ambient
negative space is the reciprocal strip space as specified by the pairing. -/
theorem spectralStripMarkushevichBasis_normalized
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    let hs₀ := le_of_lt (zero_lt_one.trans hs)
    let J := SpectralStripJetIndex χ a α s
    let Q := spectralSobolevQuotient F a (neg_nonpos.mpr hα |>.trans hα) hs₀
    let D := spectralSobolevDualEmbedding F a (neg_nonpos.mpr hα |>.trans hα) hs₀
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      (∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))) ∧
      IsNormalizedSpectralFamily (fun j ↦ D (Λ j)) := by
  obtain ⟨x, Λ, hB, hD⟩ := (spectralStripMarkushevichBasis (a := a) χ _hχ hα
    (lineHs(hs))).2
  obtain ⟨C, _, hupper⟩ := spectralStripJet_upperBound (a := a) χ _hχ hα hs
  obtain ⟨c, hc, hlower⟩ := spectralStripJet_lowerBound (a := a) χ _hχ hα hs
  refine ⟨x, Λ, hB, hD, ⟨C, ?_⟩, ⟨c, hc, ?_⟩⟩
  · intro j
    simpa only [hD j] using hupper j
  · intro j
    simpa only [hD j] using hlower j

/-- The norm integral of a strip jet does not change when the real offset changes sign. -/
private theorem spectralStripJet_order_and_margin_of_upperBound_neg (α s b : ℝ) (k : ℕ) :
    ∫ x : ℝ, Real.exp (2 * (-b) * x - 2 * α * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume =
      ∫ x : ℝ, Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
  rw [← integral_neg_eq_self (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
    ((1 + x ^ 2) ^ (s / 2))⁻¹) volume]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [abs_neg, neg_sq, (even_two_mul k).neg_pow, show 2 * b * -x = 2 * (-b) * x by ring]

/-- For a jet whose order is at least the boundary threshold, the norm integral is at least a
fixed multiple of the logarithm of the inverse distance of its real offset from the edge. -/
private theorem spectralStripJet_order_and_margin_of_upperBound_log {α s b : ℝ} {k : ℕ}
    (hs : 0 ≤ s) (hbα : b < α) (hε : α - b < 1) (hk : s ≤ 2 * (k : ℝ) + 1)
    (hint : Integrable (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹) volume) :
    Real.exp (-2) * ((2 : ℝ) ^ (s / 2))⁻¹ * Real.log (α - b)⁻¹ ≤
      ∫ x : ℝ, Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
  have hε0 : 0 < α - b := sub_pos.mpr hbα
  have hone : 1 ≤ (α - b)⁻¹ := (one_le_inv₀ hε0).mpr hε.le
  have h2pos : 0 < (2 : ℝ) ^ (s / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hg_int : Integrable ((Ioc 1 (α - b)⁻¹).indicator fun x : ℝ ↦
      Real.exp (-2) * ((2 : ℝ) ^ (s / 2))⁻¹ * x⁻¹) volume := by
    refine ((ContinuousOn.integrableOn_Icc ?_).mono_set
      Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
    exact continuousOn_const.mul
      (continuousOn_inv₀.mono fun x hx ↦ (zero_lt_one.trans_le hx.1).ne')
  have hle : ∀ x : ℝ, (Ioc 1 (α - b)⁻¹).indicator (fun x : ℝ ↦
      Real.exp (-2) * ((2 : ℝ) ^ (s / 2))⁻¹ * x⁻¹) x ≤
      Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
    intro x
    by_cases hx : x ∈ Ioc 1 (α - b)⁻¹
    · rw [indicator_of_mem hx]
      have hx1 : 1 ≤ x := hx.1.le
      have hx0 : 0 < x := zero_lt_one.trans hx.1
      have hεx : (α - b) * x ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left hx.2 hε0.le
        rwa [mul_inv_cancel₀ hε0.ne'] at h
      have hexp : Real.exp (-2) ≤ Real.exp (2 * b * x - 2 * α * |x|) := by
        rw [abs_of_pos hx0]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hD : (1 + x ^ 2) ^ (s / 2) ≤ 2 ^ (s / 2) * x ^ s := by
        calc (1 + x ^ 2) ^ (s / 2) ≤ (2 * x ^ 2) ^ (s / 2) :=
              Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
          _ = 2 ^ (s / 2) * x ^ s := by
              rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast x 2,
                ← Real.rpow_mul hx0.le]
              congr 2
              push_cast
              ring
      have hpow : x ^ s ≤ x ^ (2 * k) * x := by
        calc x ^ s ≤ x ^ ((2 * k + 1 : ℕ) : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
          _ = x ^ (2 * k) * x := by rw [Real.rpow_natCast, pow_succ]
      have hDpos : 0 < (1 + x ^ 2) ^ (s / 2) := Real.rpow_pos_of_pos (by positivity) _
      have hfrac : ((2 : ℝ) ^ (s / 2))⁻¹ * x⁻¹ ≤ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
        rw [← mul_inv, ← div_eq_mul_inv, inv_eq_one_div,
          div_le_div_iff₀ (mul_pos h2pos hx0) hDpos]
        calc 1 * (1 + x ^ 2) ^ (s / 2) ≤ 2 ^ (s / 2) * x ^ s := by rw [one_mul]; exact hD
          _ ≤ 2 ^ (s / 2) * (x ^ (2 * k) * x) := mul_le_mul_of_nonneg_left hpow h2pos.le
          _ = x ^ (2 * k) * (2 ^ (s / 2) * x) := by ring
      calc Real.exp (-2) * ((2 : ℝ) ^ (s / 2))⁻¹ * x⁻¹
          = Real.exp (-2) * (((2 : ℝ) ^ (s / 2))⁻¹ * x⁻¹) := by ring
        _ ≤ Real.exp (2 * b * x - 2 * α * |x|) *
            (x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
            mul_le_mul hexp hfrac (by positivity) (Real.exp_pos _).le
        _ = _ := by ring
    · rw [indicator_of_notMem hx]
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
  have h1 := integral_mono hg_int hint hle
  have h2 : ∫ x : ℝ, (Ioc 1 (α - b)⁻¹).indicator (fun x : ℝ ↦
      Real.exp (-2) * ((2 : ℝ) ^ (s / 2))⁻¹ * x⁻¹) x ∂volume =
      Real.exp (-2) * ((2 : ℝ) ^ (s / 2))⁻¹ * Real.log (α - b)⁻¹ := by
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hone,
      intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos
        (zero_lt_one.trans_le hone), div_one]
  linarith

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. The converse of
`spectralStripJet_upperBound_of_margin`: on one strip, a common upper bound for the norms of
the strip jets bounds their orders, and keeps the jets of order at least `(s - 1) / 2` at a
fixed distance from the two edges. So on every strip the upper bound of Proposition 10.2.2.2
is equivalent to the conclusion of `spectralStripJet_order_and_margin`.
Deviation: The paper does not state this. The squared norm of a jet of order `m` is at least
a constant times `4 ^ m`, and for `m ≥ (s - 1) / 2` at least a constant times the logarithm of
the inverse distance of its real offset from the edge. -/
theorem spectralStripJet_order_and_margin_of_upperBound
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (C : ℝ)
    (_h : ∀ j : SpectralStripJetIndex χ a α s,
      ‖(spectralStripJet_memLp χ hα (lineHs(hs)) j).toLp (stripJet(χ, j))‖ ≤ C) :
    ∃ (K : ℕ) (δ : ℝ), 0 < δ ∧ ∀ j : SpectralStripJetIndex χ a α s,
      j.val.2.2.2 ≤ K ∧ ((s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → |j.val.2.1| ≤ α - δ) := by
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let hs₀ : 0 ≤ s := lineHs(hs)
  have hfac_pos : 0 < (Measure.haarScalarFactor μ𝔽 ν : ℝ) := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν)
  let c₁ : ℝ := Real.exp (-12 * α) * ((10 : ℝ) ^ (s / 2))⁻¹
  let c₂ : ℝ := Real.exp (-2) * ((2 : ℝ) ^ (s / 2))⁻¹
  have hc₁ : 0 < c₁ :=
    mul_pos (Real.exp_pos _) (inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _))
  have hc₂ : 0 < c₂ :=
    mul_pos (Real.exp_pos _) (inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _))
  let L : ℝ := C ^ 2 / ((Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₂)
  have hL : 0 ≤ L := div_nonneg (sq_nonneg C) (mul_pos hfac_pos hc₂).le
  have hsq (j : SpectralStripJetIndex χ a α s) : (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
      ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ C ^ 2 := by
    rw [← spectralStripJet_norm_sq χ hα hs₀ j ν rfl]
    exact pow_le_pow_left₀ (norm_nonneg _) (_h j) 2
  refine ⟨⌈C ^ 2 / ((Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₁)⌉₊, Real.exp (-L),
    Real.exp_pos _, fun j ↦ ⟨?_, fun hk ↦ ?_⟩⟩
  · have hcond : (-α < j.val.2.1 ∧ j.val.2.1 < α) ∨
        ((j.val.2.1 = -α ∨ j.val.2.1 = α) ∧ 2 * (j.val.2.2.2 : ℝ) + 1 < s) := by
      have hj := j.property
      unfold spectralStripMultiplicity at hj
      split_ifs at hj with h1 h2
      · exact Or.inl h1
      · refine Or.inr ⟨h2, ?_⟩
        have horder : (j.val.2.2.2 : ℝ) < (s - 1) / 2 :=
          ((lt_spectralBoundaryMultiplicity s _ _).mp hj).2
        linarith
      · omega
    have hf_int : Integrable (fun x : ℝ ↦
        Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
          ((1 + x ^ 2) ^ (s / 2))⁻¹) volume :=
      spectralStripJet_integrable hα hs₀ hcond
    have hb : j.val.2.1 ∈ Icc (-α) α := (SpectralStripJetIndex.mem_strip_order_pos hα j).1
    have hind_int : Integrable ((Icc (2 : ℝ) 3).indicator fun _ ↦
        c₁ * 4 ^ j.val.2.2.2) volume :=
      (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    have hle : ∀ x : ℝ, (Icc (2 : ℝ) 3).indicator (fun _ ↦ c₁ * 4 ^ j.val.2.2.2) x ≤
        Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
          ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
      intro x
      by_cases hx : x ∈ Icc (2 : ℝ) 3
      · rw [indicator_of_mem hx]
        have hxpos : 0 ≤ x := by linarith [hx.1]
        have hexp : Real.exp (-12 * α) ≤ Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) := by
          rw [abs_of_nonneg hxpos]
          exact Real.exp_le_exp.mpr (by nlinarith [hb.1, hx.1, hx.2])
        have hpow : (4 : ℝ) ^ j.val.2.2.2 ≤ x ^ (2 * j.val.2.2.2) := by
          rw [pow_mul]
          exact pow_le_pow_left₀ (by norm_num) (by nlinarith [hx.1]) _
        have hbase : 1 + x ^ 2 ≤ 10 := by nlinarith [hx.1, hx.2]
        have hrpow : (1 + x ^ 2) ^ (s / 2) ≤ (10 : ℝ) ^ (s / 2) :=
          Real.rpow_le_rpow (by positivity) hbase (by linarith)
        have hinv : ((10 : ℝ) ^ (s / 2))⁻¹ ≤ ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
          inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) hrpow
        calc c₁ * 4 ^ j.val.2.2.2
            = Real.exp (-12 * α) * 4 ^ j.val.2.2.2 * ((10 : ℝ) ^ (s / 2))⁻¹ := by
              simp only [c₁]
              ring
          _ ≤ _ := mul_le_mul (mul_le_mul hexp hpow (by positivity) (Real.exp_pos _).le) hinv
              (inv_nonneg.mpr (Real.rpow_pos_of_pos (by norm_num) _).le)
              (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
      · rw [indicator_of_notMem hx]
        exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
          (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    have hint_le : c₁ * 4 ^ j.val.2.2.2 ≤ ∫ x : ℝ,
        Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
          ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
      have h1 := integral_mono hind_int hf_int hle
      have h2 : ∫ x : ℝ, (Icc (2 : ℝ) 3).indicator (fun _ ↦ c₁ * 4 ^ j.val.2.2.2) x ∂volume =
          c₁ * 4 ^ j.val.2.2.2 := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc]
        norm_num
      linarith
    have h4 : (4 : ℝ) ^ j.val.2.2.2 ≤ C ^ 2 / ((Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₁) := by
      rw [le_div_iff₀ (mul_pos hfac_pos hc₁)]
      calc (4 : ℝ) ^ j.val.2.2.2 * ((Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₁)
          = (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (c₁ * 4 ^ j.val.2.2.2) := by ring
        _ ≤ _ := (mul_le_mul_of_nonneg_left hint_le hfac_pos.le).trans (hsq j)
    have hk : (j.val.2.2.2 : ℝ) ≤ 4 ^ j.val.2.2.2 := by
      exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 4)).le
    exact Nat.cast_le.mp ((hk.trans h4).trans (Nat.le_ceil _))
  · have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with hb he
    · have habs : |j.val.2.1| < α := abs_lt.mpr hb
      by_cases h1 : 1 ≤ α - |j.val.2.1|
      · have : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        linarith
      · have hint' : Integrable (fun x : ℝ ↦
            Real.exp (2 * |j.val.2.1| * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
              ((1 + x ^ 2) ^ (s / 2))⁻¹) volume :=
          spectralStripJet_integrable hα hs₀
            (Or.inl ⟨by linarith [abs_nonneg j.val.2.1], habs⟩)
        have hlog := spectralStripJet_order_and_margin_of_upperBound_log hs₀
          habs (not_le.mp h1) (by linarith) hint'
        have hsym : ∫ x : ℝ, Real.exp (2 * |j.val.2.1| * x - 2 * α * |x|) *
            x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume =
            ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) *
              x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
          rcases abs_cases j.val.2.1 with ⟨h, _⟩ | ⟨h, _⟩
          · rw [h]
          · rw [h]
            exact spectralStripJet_order_and_margin_of_upperBound_neg α s _ _
        rw [hsym] at hlog
        have h3 : (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
            (c₂ * Real.log (α - |j.val.2.1|)⁻¹) ≤ C ^ 2 :=
          (mul_le_mul_of_nonneg_left hlog hfac_pos.le).trans (hsq j)
        have h4 : Real.log (α - |j.val.2.1|)⁻¹ ≤ L := by
          rw [le_div_iff₀ (mul_pos hfac_pos hc₂)]
          linarith
        rw [Real.log_inv] at h4
        have h5 : Real.exp (-L) ≤ α - |j.val.2.1| := by
          calc Real.exp (-L) ≤ Real.exp (Real.log (α - |j.val.2.1|)) :=
                Real.exp_le_exp.mpr (by linarith)
            _ = α - |j.val.2.1| := Real.exp_log (sub_pos.mpr habs)
        linarith
    · have hlt := ((lt_spectralBoundaryMultiplicity _ _ _).mp hj).2
      linarith
    · omega

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447, as used before (10.3.1.19),
p. 451. Among the strip jets with the same real offset, a jet of lower order has norm at most a
fixed multiple of the norm of a jet of higher order. So the products of the norm of a jet and
the norm of the biorthogonal vector of a jet of higher order at the same zero, for which
p. 451 asks one constant, are bounded by the products with equal orders. No bound on the
multiplicities of the zeros is used.
Deviation: The paper does not state this. It takes the bound from an upper bound for the norms
of all the jets. -/
theorem spectralStripJet_norm_le_of_order_le (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ j j' : SpectralStripJetIndex χ a α s,
      j'.val.2.1 = j.val.2.1 → j'.val.2.2.2 ≤ j.val.2.2.2 →
      ‖(spectralStripJet_memLp χ hα (lineHs(hs)) j').toLp (stripJet(χ, j'))‖ ≤
        C * ‖(spectralStripJet_memLp χ hα (lineHs(hs)) j).toLp (stripJet(χ, j))‖ := by
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let hs₀ : 0 ≤ s := lineHs(hs)
  have hfac_nonneg : 0 ≤ (Measure.haarScalarFactor μ𝔽 ν : ℝ) := NNReal.coe_nonneg _
  obtain ⟨c, hc, hlower⟩ := spectralStripJet_lowerBound (a := a) χ _hχ hα hs
  let I₀ : ℝ := ∫ x : ℝ, ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume
  have hI₀_int : Integrable (fun x : ℝ ↦ ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := by
    have h := integrable_pow_mul_rpow_inv (k := 0) (s := s) (by
      rw [Nat.cast_zero, mul_zero, zero_add]
      exact hs)
    simpa only [mul_zero, pow_zero, one_mul] using h
  have hI₀ : 0 ≤ I₀ := integral_nonneg fun x ↦
    inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le
  let B : ℝ := (Measure.haarScalarFactor μ𝔽 ν : ℝ) * I₀ / c ^ 2 + 1
  have hB : 0 < B := by
    have : 0 ≤ (Measure.haarScalarFactor μ𝔽 ν : ℝ) * I₀ / c ^ 2 :=
      div_nonneg (mul_nonneg hfac_nonneg hI₀) (sq_nonneg c)
    linarith
  refine ⟨Real.sqrt B, Real.sqrt_pos.mpr hB, fun j j' hb hm ↦ ?_⟩
  have hcond (i : SpectralStripJetIndex χ a α s) : (-α < i.val.2.1 ∧ i.val.2.1 < α) ∨
      ((i.val.2.1 = -α ∨ i.val.2.1 = α) ∧ 2 * (i.val.2.2.2 : ℝ) + 1 < s) := by
    have hi := i.property
    unfold spectralStripMultiplicity at hi
    split_ifs at hi with h1 h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2, ?_⟩
      have horder : (i.val.2.2.2 : ℝ) < (s - 1) / 2 :=
        ((lt_spectralBoundaryMultiplicity s _ _).mp hi).2
      linarith
    · omega
  have hcond₀ : (-α < j.val.2.1 ∧ j.val.2.1 < α) ∨
      ((j.val.2.1 = -α ∨ j.val.2.1 = α) ∧ 2 * ((0 : ℕ) : ℝ) + 1 < s) := by
    rcases hcond j with h | ⟨h, -⟩
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      rw [Nat.cast_zero, mul_zero, zero_add]
      exact hs
  have hint : Integrable (fun x : ℝ ↦
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := spectralStripJet_integrable hα hs₀ (hcond j)
  have hint' : Integrable (fun x : ℝ ↦
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j'.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := by
    have h := spectralStripJet_integrable hα hs₀ (hcond j')
    rwa [hb] at h
  have hint₀ : Integrable (fun x : ℝ ↦
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * 0) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := spectralStripJet_integrable hα hs₀ hcond₀
  have hbα : j.val.2.1 ∈ Icc (-α) α := (SpectralStripJetIndex.mem_strip_order_pos hα j).1
  have hpos (x : ℝ) : 0 ≤ ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
    inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le
  -- The zeroth jet has a norm integral bounded independently of the offset.
  have h₀ : ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * 0) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ I₀ := by
    refine integral_mono hint₀ hI₀_int fun x ↦ ?_
    have hbx : j.val.2.1 * x ≤ α * |x| := by
      calc
        j.val.2.1 * x ≤ |j.val.2.1 * x| := le_abs_self _
        _ = |j.val.2.1| * |x| := abs_mul _ _
        _ ≤ α * |x| := mul_le_mul_of_nonneg_right (abs_le.mpr hbα) (abs_nonneg x)
    have hexp : Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    calc Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * 0) * ((1 + x ^ 2) ^ (s / 2))⁻¹
        = Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
          rw [mul_zero, pow_zero, mul_one]
      _ ≤ 1 * ((1 + x ^ 2) ^ (s / 2))⁻¹ := mul_le_mul_of_nonneg_right hexp (hpos x)
      _ = ((1 + x ^ 2) ^ (s / 2))⁻¹ := one_mul _
  -- A lower power is at most one plus a higher power.
  have hle : ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j'.val.2.2.2) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤
      (∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * 0) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume) +
      ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
    rw [← integral_add hint₀ hint]
    refine integral_mono hint' (hint₀.add hint) fun x ↦ ?_
    have hpow : x ^ (2 * j'.val.2.2.2) ≤ x ^ (2 * 0) + x ^ (2 * j.val.2.2.2) := by
      have hxa : x ^ (2 * j'.val.2.2.2) = |x| ^ (2 * j'.val.2.2.2) := by
        rw [pow_mul, ← sq_abs, ← pow_mul]
      have hxaK : x ^ (2 * j.val.2.2.2) = |x| ^ (2 * j.val.2.2.2) := by
        rw [pow_mul, ← sq_abs, ← pow_mul]
      rw [hxa, hxaK, mul_zero, pow_zero]
      rcases le_total |x| 1 with hx1 | hx1
      · have : |x| ^ (2 * j'.val.2.2.2) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
        linarith [pow_nonneg (abs_nonneg x) (2 * j.val.2.2.2)]
      · have : |x| ^ (2 * j'.val.2.2.2) ≤ |x| ^ (2 * j.val.2.2.2) :=
          pow_le_pow_right₀ hx1 (Nat.mul_le_mul_left 2 hm)
        linarith
    calc Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j'.val.2.2.2) *
          ((1 + x ^ 2) ^ (s / 2))⁻¹
        ≤ Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) *
            (x ^ (2 * 0) + x ^ (2 * j.val.2.2.2)) * ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le) (hpos x)
      _ = _ := by ring
  have hsq := spectralStripJet_norm_sq χ hα hs₀ j ν rfl
  have hsq' : ‖(spectralStripJet_memLp χ hα hs₀ j').toLp (stripJet(χ, j'))‖ ^ 2 =
      (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
        ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j'.val.2.2.2) *
          ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
    rw [spectralStripJet_norm_sq χ hα hs₀ j' ν rfl, hb]
  have hc2 : c ^ 2 ≤ ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2 :=
    pow_le_pow_left₀ hc.le (hlower j) 2
  have hmain : ‖(spectralStripJet_memLp χ hα hs₀ j').toLp (stripJet(χ, j'))‖ ^ 2 ≤
      B * ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2 := by
    have h1 : ‖(spectralStripJet_memLp χ hα hs₀ j').toLp (stripJet(χ, j'))‖ ^ 2 ≤
        (Measure.haarScalarFactor μ𝔽 ν : ℝ) * I₀ +
          ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2 := by
      rw [hsq', hsq, ← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith) hfac_nonneg
    have h2 : (Measure.haarScalarFactor μ𝔽 ν : ℝ) * I₀ ≤
        (Measure.haarScalarFactor μ𝔽 ν : ℝ) * I₀ / c ^ 2 *
          ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2 := by
      calc (Measure.haarScalarFactor μ𝔽 ν : ℝ) * I₀
          = (Measure.haarScalarFactor μ𝔽 ν : ℝ) * I₀ / c ^ 2 * c ^ 2 := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hc2
            (div_nonneg (mul_nonneg hfac_nonneg hI₀) (sq_nonneg c))
    calc ‖(spectralStripJet_memLp χ hα hs₀ j').toLp (stripJet(χ, j'))‖ ^ 2
        ≤ (Measure.haarScalarFactor μ𝔽 ν : ℝ) * I₀ / c ^ 2 *
            ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2 +
          ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2 := by linarith
      _ = B * ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖ ^ 2 := by
          simp only [B]
          ring
  have hfinal : ‖(spectralStripJet_memLp χ hα hs₀ j').toLp (stripJet(χ, j'))‖ ^ 2 ≤
      (Real.sqrt B * ‖(spectralStripJet_memLp χ hα hs₀ j).toLp (stripJet(χ, j))‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hB.le]
    exact hmain
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) two_ne_zero).mp hfinal

end RiemannMasullo

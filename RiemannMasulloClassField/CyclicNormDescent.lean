module

public import Mathlib.Topology.Algebra.PontryaginDual
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.StandardNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardClassComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivIdeleClassTopology
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardGaloisNorm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardGaloisDescent
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.StandardIdeleClassTate
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import RiemannMasullo.Ch03_IdelicZeta.Sec1
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual

/-! # Descent of invariant unitary idèle-class characters through a cyclic norm -/

public noncomputable section

open NumberField Function Set Topology
open scoped NNReal NumberField
open CyclicCohomology.ProfiniteCohomology.Herbrand

namespace RiemannMasullo

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local notation "C[" T "]" => NumberField.IdeleClassGroup (𝓞 T) T
local notation "N" => NumberField.IdeleClassGroup.norm K L
local notation "Nᶜ" => NumberField.IdeleClassGroup.normContinuousMonoidHom K L

/-- For a finite cyclic extension, the actual relative norm kernel consists exactly
of the coboundaries of a generator, written in the project's usual idèle class group. -/
theorem cyclicIdeleClassNorm_kernel (σ : Gal(L/K)) (hσ : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ)
    (x : C[L]) : N x = 1 ↔ ∃ y : C[L], NumberField.IdeleClassGroup.congr (σ.restrictScalars ℚ) y * y⁻¹ = x := by
  let := NumberField.IdeleClassGroup.relativeGaloisAction K L
  have h := (GlobalClassFieldTheory.ClassFieldAxiom.standardIdeleClass_lowDegree_card_eq_finrank_cyclic K L σ hσ).2
  have ht := (herbrandHMinusOne_subsingleton_iff_normKernel_le_augmentationSubgroup
    (G := Gal(L/K)) (A := C[L]) σ).1 (Nat.card_eq_one_iff_unique.mp h).1
  have hx : N x = 1 ↔ x ∈ normKernelSubgroup (Gal(L/K)) C[L] := by
    change N x = 1 ↔ tateNorm (Gal(L/K)) C[L] x = 1
    have hi : NumberField.IdeleClassGroup.fieldInclusion K L (N x) = tateNorm (Gal(L/K)) C[L] x :=
      NumberField.IdeleClassGroup.fieldInclusion_norm_eq_prod_congr K L x
    rw [← hi, ← (NumberField.IdeleClassGroup.fieldInclusion K L).map_one]
    exact (NumberField.IdeleClassGroup.fieldInclusion_injective K L).eq_iff.symm
  exact hx.trans ⟨fun h ↦ ht h, fun h ↦ augmentationSubgroup_le_normKernelSubgroup σ h⟩

private theorem sigmaCompact_standard_classes (F : Type*) [Field F] [NumberField F] :
    SigmaCompactSpace C[F] := by
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let : SigmaCompactSpace ℝ≥0ˣ := e.symm.isClosedEmbedding.sigmaCompactSpace
  refine SigmaCompactSpace_iff_exists_compact_covering.mpr ⟨fun n ↦
    (ideleClassNorm F) ⁻¹' compactCovering ℝ≥0ˣ n, fun n ↦ ?_, ?_⟩
  · exact (isProperMap_ideleClassNorm F).isCompact_preimage (isCompact_compactCovering _ n)
  · rw [← preimage_iUnion, iUnion_compactCovering, preimage_univ]

/-- The continuous field norm is an open quotient onto its actual norm subgroup. -/
theorem relativeIdeleClassNorm_openQuotient :
    IsOpenQuotientMap (N).rangeRestrict := by
  let : SigmaCompactSpace C[L] := sigmaCompact_standard_classes L
  let : LocallyCompactSpace C[K] := (ideleGroup_quotient.{_, 0} K).2.2.2.2.2.2.1
  let : T2Space C[K] := (ideleGroup_quotient.{_, 0} K).2.2.2.2.2.1
  let : LocallyCompactSpace (N).range :=
    (GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_range_isOpen
      (K := K) (L := L)).isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hc : Continuous (N).rangeRestrict := (Nᶜ).continuous.subtype_mk _
  exact ⟨(N).rangeRestrict_surjective, hc, (N).rangeRestrict.isOpenMap_of_sigmaCompact
    (N).rangeRestrict_surjective hc⟩

/-- A unitary character of any order on the full upper idèle class group descends
through the actual relative norm exactly when it is invariant under a cyclic generator. -/
theorem cyclicIdeleClassCharacter_norm_descent (σ : Gal(L/K))
    (hσ : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ) (ψ : PontryaginDual C[L]) :
    (∃ χ : PontryaginDual C[K], ∀ x : C[L], χ (N x) = ψ x) ↔
      ∀ x : C[L], ψ (NumberField.IdeleClassGroup.congr (σ.restrictScalars ℚ) x) = ψ x := by
  constructor
  · rintro ⟨χ, hχ⟩ x
    rw [← hχ, ← hχ]
    exact congrArg χ <| by
      have h := NumberField.IdeleClassGroup.norm_congr_of_compatible K L
        (AlgEquiv.refl : K ≃ₐ[ℚ] K) (σ.restrictScalars ℚ) (fun z ↦ σ.commutes z) x
      simpa only [NumberField.IdeleClassGroup.congr_refl] using h.symm
  · intro hinv
    let : LocallyCompactSpace C[K] := (ideleGroup_quotient.{_, 0} K).2.2.2.2.2.2.1
    let f := (N).rangeRestrict
    have hker : f.ker ≤ ψ.toMonoidHom.ker := by
      intro x hx
      have hn : N x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      obtain ⟨y, rfl⟩ := (cyclicIdeleClassNorm_kernel K L σ hσ x).mp hn
      exact MonoidHom.mem_ker.mpr (by change ψ (_ * _) = 1; rw [map_mul, map_inv, hinv, mul_inv_cancel])
    let s := surjInv (N).rangeRestrict_surjective
    let e := f.liftOfRightInverse s (rightInverse_surjInv _) ⟨ψ.toMonoidHom, hker⟩
    have he (x : C[L]) : e (f x) = ψ x := f.liftOfRightInverse_comp_apply _ _ _ x
    have hc : Continuous e := (relativeIdeleClassNorm_openQuotient K L).isQuotientMap.continuous_iff.mpr
      (show Continuous (e ∘ f) from ψ.continuous.congr (fun x ↦ (he x).symm))
    let η : PontryaginDual (N).range := ⟨e, hc⟩
    obtain ⟨χ, hχ, _⟩ := exists_pontryaginDual_extension_trivial_on_compact (N).range ⊥
      (GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_range_isClosed (K := K) (L := L))
      (by simp) η (fun x hx ↦ by
        have hx1 : x = 1 := Subtype.ext (Subgroup.mem_bot.mp hx)
        rw [hx1, map_one])
    exact ⟨χ, fun x ↦ (hχ (f x)).trans (he x)⟩

/-- The full unitary norm twists for a finite cyclic extension form a kernel of size
equal to its degree. This count applies to twists of a character of arbitrary order. -/
theorem cyclicIdeleClass_normPullback_kernel_card [IsCyclic (Gal(L/K))] :
    Nat.card (PontryaginDual.map Nᶜ).toMonoidHom.ker = Module.finrank K L := by
  let : LocallyCompactSpace C[K] := (ideleGroup_quotient.{_, 0} K).2.2.2.2.2.2.1
  let : T2Space C[K] := (ideleGroup_quotient.{_, 0} K).2.2.2.2.2.1
  let H := (N).range
  let Q := C[K] ⧸ H
  have hH : IsClosed (H : Set C[K]) :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_range_isClosed (K := K) (L := L)
  let : H.FiniteIndex := GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex
  let : Finite Q := inferInstanceAs (Finite (C[K] ⧸ H))
  let : DiscreteTopology Q :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotient_discreteTopology
  have hker : (PontryaginDual.map Nᶜ).toMonoidHom.ker = lcaAnnihilator H := by
    ext χ
    rw [MonoidHom.mem_ker, mem_lcaAnnihilator_iff]
    constructor
    · rintro h ⟨_, x, rfl⟩
      exact DFunLike.congr_fun h x
    · intro h
      exact PontryaginDual.ext fun x ↦ h ⟨N x, x, rfl⟩
  obtain ⟨e, _⟩ := lcaQuotientDual_equiv_annihilator H hH
  let d : PontryaginDual Q ≃ (Q →* Circle) :=
    ⟨fun χ ↦ χ.toMonoidHom, fun χ ↦ ⟨χ, continuous_of_discreteTopology⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  calc
    Nat.card (PontryaginDual.map Nᶜ).toMonoidHom.ker = Nat.card (PontryaginDual Q) := by
      rw [hker]
      exact Nat.card_congr e.toEquiv.symm
    _ = Nat.card (Q →* Circleˣ) := Nat.card_congr (d.trans MonoidHom.toHomUnitsMulEquiv.toEquiv)
    _ = Nat.card Q := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q Circle
    _ = Module.finrank K L := GlobalClassFieldTheory.ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic K L

/-- In a prime-degree Galois step all true unitary norm twists can be enumerated
by the relative degree, with the trivial twist in position zero. -/
theorem primeDegree_ideleClass_normTwist_indexing (hprime : (Module.finrank K L).Prime) :
    ∃ e : Fin (Module.finrank K L) ≃ (PontryaginDual.map Nᶜ).toMonoidHom.ker,
      e ⟨0, Module.finrank_pos⟩ = 1 := by
  classical
  let : Fact (Module.finrank K L).Prime := ⟨hprime⟩
  let : IsCyclic (Gal(L/K)) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K L)
  have hc := cyclicIdeleClass_normPullback_kernel_card K L
  let e := (finCongr hc.symm).trans (Nat.equivFinOfCardPos (hc.trans_ne Module.finrank_pos.ne')).symm
  let i : Fin (Module.finrank K L) := ⟨0, Module.finrank_pos⟩
  refine ⟨(Equiv.swap i (e.symm 1)).trans e, ?_⟩
  change e (Equiv.swap i (e.symm 1) i) = 1
  rw [Equiv.swap_apply_left, e.apply_symm_apply]

section PrimeNormDescent

variable (F : Type*) [Field F] [NumberField F]

/-- A nonidentity arithmetic automorphism fixing a unitary character gives a prime-degree
cyclic subextension of descent. The upper number field need not be Galois over the rationals. -/
theorem exists_primeDegree_norm_descent_of_nontrivial_stabilizer
    (ψ : PontryaginDual C[F])
    (h : ¬ ∀ σ : Gal(F/ℚ), ψ.comp (NumberField.IdeleClassGroup.congrContinuousMulEquiv σ) = ψ → σ = 1) :
    ∃ E : { E : IntermediateField ℚ F // IsGalois E F ∧ (Module.finrank E F).Prime },
      ∃ χ : PontryaginDual C[E.val], χ.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom E.val F) = ψ := by
  classical
  push Not at h
  obtain ⟨σ, hinv, hne⟩ := h
  let := NumberField.IdeleClassGroup.relativeGaloisAction ℚ F
  have hfix (n : ℕ) (x : C[F]) : ψ ((σ^n) • x) = ψ x := by
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_smul, ih]
      exact DFunLike.congr_fun hinv x
  let p := (orderOf σ).minFac
  have hp : p.Prime := Nat.minFac_prime (orderOf_eq_one_iff.not.mpr hne)
  let g := σ ^ (orderOf σ / p)
  have hg : orderOf g = p := orderOf_pow_orderOf_div (orderOf_pos σ).ne' (Nat.minFac_dvd _)
  let H := Subgroup.zpowers g
  let E := IntermediateField.fixedField H
  have hdeg : Module.finrank E F = p := (IntermediateField.finrank_fixedField_eq_card H).trans
    ((Nat.card_zpowers g).trans hg)
  let : IsGalois E F := inferInstanceAs (IsGalois (FixedPoints.subfield H F) F)
  let e : H ≃* Gal(F/E) := IntermediateField.subgroupEquivAlgEquiv H
  let s : H := ⟨g, Subgroup.mem_zpowers g⟩
  have hgen (τ : Gal(F/E)) : τ ∈ Subgroup.zpowers (e s) := by
    obtain ⟨n, hn⟩ := (e.symm τ).property
    refine ⟨n, ?_⟩
    change e s ^ n = τ
    rw [← map_zpow]
    exact (congrArg e (Subtype.ext hn)).trans (e.apply_symm_apply τ)
  have hagree : (e s).restrictScalars ℚ = g := AlgEquiv.ext fun _ ↦ rfl
  refine ⟨⟨E, inferInstance, hdeg ▸ hp⟩, ?_⟩
  obtain ⟨χ, hχ⟩ := (cyclicIdeleClassCharacter_norm_descent E F (e s) hgen ψ).mpr (fun x ↦ by
    rw [hagree]
    exact hfix _ x)
  exact ⟨χ, PontryaginDual.ext hχ⟩

end PrimeNormDescent

end RiemannMasullo

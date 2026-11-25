module

public import RiemannMasullo.Ch06_LocalGlobal.Sec3_HeckeProductMultiplicities
public import RiemannMasullo.ForMathlib.GroupTheory.FiniteAbelian.CharacterEulerProduct
public import RiemannMasulloClassField.HeckeNormLocalValues
public import RiemannMasulloClassField.NormPrimeFrobenius
import RiemannMasullo.Ch03_IdelicZeta.Sec1
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Ramification.FiniteRamifiedPrimes
import Mathlib.NumberTheory.RamificationInertia.Galois

/-! # Positive completed Hecke divisors under abelian base change

For a finite abelian extension and any continuous unitary character of the base, the
positive order of its norm pullback equals the sum over all characters of the relative
idèle class norm quotient. The local calculation uses the actual unramified Frobenius
and the determinant over the finite dual. The omitted finite Euler factors have no
zeros or poles on the open critical strip. See Tate, *Number theoretic background*
(1979), §§2.3.2 and 3.3.2, p. 14. -/

@[expose] public noncomputable section

open NumberField Set IsDedekindDomain
open scoped NumberField.AdeleRing

namespace RiemannMasullo

variable {E F : Type*} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
local notation "V[" K "]" => HeightOneSpectrum (𝓞 K)
local notation "U[" K "]" => PontryaginDual (NumberField.IdeleClassGroup (𝓞 K) K)

private theorem unitary_unramified_cofinite {K : Type*} [Field K] [NumberField K] (χ : U[K]) :
    ∀ᶠ v : V[K] in Filter.cofinite, (ideleClassNormTwist χ 0).IsUnramifiedAt v := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (V[K]), ideleClassNormTwist χ 0 ∈ unramifiedOutside K S :=
    Set.mem_iUnion.mp ((iUnion_unramifiedOutside K).symm ▸ Set.mem_univ _)
  exact Filter.eventually_cofinite.mpr <| S.finite_toSet.subset fun v h ↦
    by_contra fun hv ↦ h (hS v hv)

private theorem prime_fiber_liesOver {v : V[E]} {w : V[F]} (h : w.under (𝓞 E) = v) :
    w.asIdeal.LiesOver v.asIdeal := by
  exact ⟨(congrArg HeightOneSpectrum.asIdeal h).symm⟩

private theorem eventually_unramified_prime_fibres {ι : Type*} [Finite ι] (low : ι → U[E]) :
    ∀ᶠ v : V[E] in Filter.cofinite,
      (∀ w : V[F], w.under (𝓞 E) = v → Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal) ∧
      ∀ i, (ideleClassNormTwist (low i) 0).IsUnramifiedAt v := by
  classical
  have lower : ∀ᶠ v : V[E] in Filter.cofinite, ∀ i, (ideleClassNormTwist (low i) 0).IsUnramifiedAt v :=
    Filter.eventually_all.mpr (fun i ↦ unitary_unramified_cofinite (low i))
  have he := AlgebraicNumberTheory.Ramification.finite_ramified_base_heightOne_primes (𝓞 E) (𝓞 F)
  filter_upwards [lower, he.compl_mem_cofinite] with v hv h
  exact ⟨fun w hw ↦ by_contra (fun h' ↦ h ⟨w, prime_fiber_liesOver hw, h'⟩), hv⟩

private def primeFiberEquiv (v : V[E]) :
    {w : V[F] // w.under (𝓞 E) = v} ≃ (v.asIdeal.primesOver (𝓞 F)) where
  toFun w := ⟨w.val.asIdeal, w.val.isPrime, prime_fiber_liesOver w.property⟩
  invFun Q := ⟨⟨Q.val, Q.property.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot Q.property⟩,
    HeightOneSpectrum.ext Q.property.2.over.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem primeFiber_card_of_unramified [IsGalois E F] (v : V[E])
    (h : ∀ w : V[F], w.under (𝓞 E) = v → Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal) :
    Nat.card {w : V[F] // w.under (𝓞 E) = v} =
      Module.finrank E F / v.asIdeal.inertiaDegIn (𝓞 F) := by
  classical
  let T := v.asIdeal.primesOver (𝓞 F)
  let : Fintype T := Fintype.ofFinite _
  obtain ⟨q⟩ : Nonempty T := inferInstance
  have : Algebra.IsUnramifiedAt (𝓞 E) q.val := h ((primeFiberEquiv v).symm q).val
    ((primeFiberEquiv v).symm q).property
  have er : v.asIdeal.ramificationIdxIn (𝓞 F) = 1 :=
    (Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal q.val Gal(F/E)).trans
      (Ideal.ramificationIdx_eq_one q.val (𝓞 E))
  have pos : 0 < v.asIdeal.inertiaDegIn (𝓞 F) := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal q.val Gal(F/E)]
    exact Ideal.inertiaDeg_pos q.val (𝓞 E)
  have eq := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 F) Gal(F/E)
  rw [er, one_mul, IsGalois.card_aut_eq_finrank] at eq
  rw [Nat.card_congr (primeFiberEquiv v), ← eq, Nat.mul_div_cancel _ pos]
  exact Nat.card_eq_fintype_card.trans (Set.fintypeCard_eq_ncard _)

private theorem complex_nat_pow_cpow (q f : ℕ) (s : ℂ) :
    ((q ^ f : ℕ) : ℂ) ^ s = ((q : ℂ) ^ s) ^ f := by
  rw [← Complex.cpow_nat_mul, ← Complex.ofReal_natCast q]
  simpa only [← Complex.ofReal_natCast, Real.rpow_natCast, Nat.cast_pow, Complex.ofReal_pow] using
    (Complex.cpow_mul_ofReal_nonneg (Nat.cast_nonneg q) (f : ℝ) s).symm

private theorem unitary_value_at_chosen (ν : U[E]) (v : V[E])
    (h : (ideleClassNormTwist ν 0).IsUnramifiedAt v) :
    (ideleClassNormTwist ν 0).localValue v =
      (ν (IdeleGroup.finitePlaceIdeleClass v (FiniteIdeleGroup.chosenLocalOrderSection v 1)) : ℂ) := by
  rw [h.localValue_eq _ (chosenLocalOrderSection_one_isUniformizer v), HeckeCharacter.restrict,
    MulChar.ofUnitHom_coe]
  change (ν _ : ℂ) * _ ^ (0 : ℂ) = _
  rw [Complex.cpow_zero, mul_one]

private theorem finitePlaceBelow_eq_under (w : V[F]) :
    _root_.finitePlaceBelow (K := E) w = w.under (𝓞 E) := HeightOneSpectrum.ext rfl

/-- Local Artin factorization at an unramified finite prime of an abelian extension.
The formula uses the project's ordinary finite Euler factors on both sides. -/
private theorem abelianEuler_good_prime [IsAbelianGalois E F]
    {ι : Type*} [Fintype ι]
    (e : ι ≃ (PontryaginDual.map (NumberField.IdeleClassGroup.normContinuousMonoidHom E F)).toMonoidHom.ker)
    (ν : U[E]) (v : V[E])
    (hν : (ideleClassNormTwist ν 0).IsUnramifiedAt v)
    (hνi : ∀ i, (ideleClassNormTwist (ν * (e i).val) 0).IsUnramifiedAt v)
    (hun : ∀ w : V[F], w.under (𝓞 E) = v → Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal)
    (hfrob : ∀ w : {w : V[F] // w.under (𝓞 E) = v},
      orderOf (relativeNormPrimeClass E F v) = w.val.asIdeal.inertiaDeg (𝓞 E))
    (s : {z : ℂ // 1 < z.re}) :
    (∏' w : {w : V[F] // w.under (𝓞 E) = v},
        finiteHeckeEulerFactor (ν.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom E F)) w.val s) =
      ∏ i, finiteHeckeEulerFactor (ν * (e i).val) v s := by
  classical
  let N := NumberField.IdeleClassGroup.normContinuousMonoidHom E F
  let Q := NumberField.IdeleClassGroup (𝓞 E) E ⧸ N.toMonoidHom.range
  let : N.toMonoidHom.range.FiniteIndex :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex
  let : Finite Q := inferInstance
  let : DiscreteTopology Q :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotient_discreteTopology
  let W := {w : V[F] // w.under (𝓞 E) = v}
  let : Fintype W := (finite_places_over_finite (F := F) v).fintype
  let f := v.asIdeal.inertiaDegIn (𝓞 F)
  let g := IdeleGroup.finitePlaceIdeleClass v (FiniteIdeleGroup.chosenLocalOrderSection v 1)
  let X := (ν g : ℂ) * (v.asIdeal.absNorm : ℂ) ^ (-(s : ℂ))
  have hdeg (w : W) : w.val.asIdeal.inertiaDeg (𝓞 E) = f := by
    let : w.val.asIdeal.LiesOver v.asIdeal := prime_fiber_liesOver w.property
    exact (Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.val.asIdeal Gal(F/E)).symm
  obtain ⟨q⟩ : Nonempty (v.asIdeal.primesOver (𝓞 F)) := inferInstance
  let q' : W := (primeFiberEquiv v).symm q
  have ho : orderOf (relativeNormPrimeClass E F v) = f := (hfrob q').trans (hdeg q')
  have hc : Nat.card Q = Module.finrank E F :=
    (Nat.card_congr
      (GlobalClassFieldTheory.Reciprocity.standardNumberFieldNormResidueContinuousMulEquiv E F).toEquiv).trans
      (IsGalois.card_aut_eq_finrank E F)
  have htop (w : W) : finiteHeckeEulerFactor (ν.comp N) w.val s = (1 - X ^ f)⁻¹ := by
    let : w.val.asIdeal.LiesOver v.asIdeal := prime_fiber_liesOver w.property
    have hw := unitary_normPullback_localValue (L := F) ν v hν
      ⟨w.val, (finitePlaceBelow_eq_under w.val).trans w.property⟩
    let χ := ν.comp N
    have hun' : (ideleClassNormTwist χ 0).IsUnramifiedAt w.val := hw.1
    have hv' : (ideleClassNormTwist χ 0).localValue w.val =
        (ideleClassNormTwist ν 0).localValue v ^ w.val.asIdeal.inertiaDeg (𝓞 E) := hw.2
    change (if (ideleClassNormTwist χ 0).IsUnramifiedAt w.val then
      (1 - (ideleClassNormTwist χ 0).localValue w.val * (w.val.asIdeal.absNorm : ℂ) ^ (-(s : ℂ)))⁻¹
      else 1) = (1 - X ^ f)⁻¹
    rw [ite_eq_left hun', hv', ← Ideal.absNorm_pow_inertiaDeg v.asIdeal w.val.asIdeal,
      hdeg w, complex_nat_pow_cpow, ← mul_pow, unitary_value_at_chosen ν v hν]
  have hdown (i : ι) : finiteHeckeEulerFactor (ν * (e i).val) v s =
      (1 - X * ((e i).val g : ℂ))⁻¹ := by
    rw [finiteHeckeEulerFactor, ite_eq_left (hνi i), unitary_value_at_chosen _ _ (hνi i)]
    change (1 - ((ν g : ℂ) * ((e i).val g : ℂ)) * _)⁻¹ = _
    dsimp only [X]
    ring
  have hprod := prod_one_sub_pullbackKernel_apply N e g X
  change (∏ i, (1 - X * ((e i).val g : ℂ))) = (1 - X ^ orderOf (relativeNormPrimeClass E F v)) ^
      (Nat.card Q / orderOf (relativeNormPrimeClass E F v)) at hprod
  rw [ho, hc] at hprod
  change (∏' w : W, finiteHeckeEulerFactor (ν.comp N) w.val s) = _
  rw [tprod_fintype, Finset.prod_congr rfl (fun w _ ↦ htop w),
    Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card, primeFiber_card_of_unramified v hun]
  simp_rw [hdown]
  rw [Finset.prod_inv_distrib, hprod, inv_pow]

/-- The actual Euler comparison outside finitely many base places, for every finite
abelian field extension and every unitary Hecke character. -/
theorem abelian_normPullback_EulerFactors_off_finset [IsAbelianGalois E F]
    {ι : Type*} [Fintype ι]
    (e : ι ≃ (PontryaginDual.map (NumberField.IdeleClassGroup.normContinuousMonoidHom E F)).toMonoidHom.ker)
    (ν : U[E]) :
    ∃ B : Finset (V[E]), ∀ v ∉ B, ∀ s : {z : ℂ // 1 < z.re},
      (∏' w : {w : V[F] // w.under (𝓞 E) = v},
        finiteHeckeEulerFactor (ν.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom E F)) w.val s) =
        ∏ i, finiteHeckeEulerFactor (ν * (e i).val) v s := by
  classical
  let N := NumberField.IdeleClassGroup.normContinuousMonoidHom E F
  let low : Option ι → U[E] := fun i ↦ i.elim ν (fun j ↦ ν * (e j).val)
  have hfree := eventually_unramified_prime_fibres (F := F) low
  obtain ⟨S, hS⟩ := exists_finset_orderOf_relativeNormPrimeClass_eq_inertiaDeg E F
  have good : ∀ᶠ v : V[E] in Filter.cofinite, ∀ s : {z : ℂ // 1 < z.re},
      (∏' w : {w : V[F] // w.under (𝓞 E) = v}, finiteHeckeEulerFactor (ν.comp N) w.val s) =
        ∏ i, finiteHeckeEulerFactor (ν * (e i).val) v s := by
    filter_upwards [hfree, S.finite_toSet.compl_mem_cofinite] with v hv hs
    exact abelianEuler_good_prime e ν v (hv.2 none) (fun i ↦ hv.2 (some i)) hv.1
      (fun w ↦ hS v hs ⟨w.val, (finitePlaceBelow_eq_under w.val).trans w.property⟩)
  let bad := Filter.eventually_cofinite.mp good
  refine ⟨bad.toFinset, fun v hv ↦ ?_⟩
  exact of_not_not fun hn ↦ hv (bad.mem_toFinset.mpr hn)

/-- The true completed multiplicity of a unitary norm pullback is the sum of the
multiplicities of all its twists for any finite abelian extension. -/
theorem abelian_normPullback_multiplicity [IsAbelianGalois E F] {ι : Type*} [Fintype ι]
    (e : ι ≃ (PontryaginDual.map (NumberField.IdeleClassGroup.normContinuousMonoidHom E F)).toMonoidHom.ker)
    (ν : U[E]) (z : ℂ) :
    (meromorphicOrderAt (continuedCompletedHeckeL
      (ν.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom E F))) z).untop₀.toNat =
      ∑ i, (meromorphicOrderAt (continuedCompletedHeckeL (ν * (e i).val)) z).untop₀.toNat := by
  obtain ⟨B, hB⟩ := abelian_normPullback_EulerFactors_off_finset e ν
  exact spectralZeroMultiplicity_eq_sum_of_localEulerFactors_off_finset _ _ B hB z

/-- The lower factors can be indexed directly by the full norm-trivial unitary dual.
The sum is finite and counts every twist, including the trivial one. -/
theorem abelian_normPullback_multiplicity_eq_tsum [IsAbelianGalois E F] (ν : U[E]) (z : ℂ) :
    (meromorphicOrderAt (continuedCompletedHeckeL
      (ν.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom E F))) z).untop₀.toNat =
      ∑' θ : (PontryaginDual.map (NumberField.IdeleClassGroup.normContinuousMonoidHom E F)).toMonoidHom.ker,
        (meromorphicOrderAt (continuedCompletedHeckeL (ν * θ.val)) z).untop₀.toNat := by
  classical
  let N := NumberField.IdeleClassGroup.normContinuousMonoidHom E F
  let Q := NumberField.IdeleClassGroup (𝓞 E) E ⧸ N.toMonoidHom.range
  let T := (PontryaginDual.map N).toMonoidHom.ker
  let : N.toMonoidHom.range.FiniteIndex :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex
  let : Finite Q := inferInstance
  let : DiscreteTopology Q :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotient_discreteTopology
  have hc : Nat.card T = Nat.card Q :=
    (Nat.card_congr ((pullbackKernelEquivQuotientCircleHom N).trans
      MonoidHom.toHomUnitsMulEquiv.toEquiv)).trans (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q Circle)
  let : Finite T := (Nat.card_pos_iff.mp (hc.symm ▸ Nat.card_pos (α := Q))).2
  let : Fintype T := Fintype.ofFinite _
  change _ = ∑' θ : T, _
  rw [tsum_fintype]
  exact abelian_normPullback_multiplicity (Equiv.refl T) ν z

end RiemannMasullo

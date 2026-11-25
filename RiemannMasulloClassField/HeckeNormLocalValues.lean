module

public import RiemannMasullo.Ch03_IdelicZeta.Sec2
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.StandardNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.OnePlaceBaseNorm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormLocalOrder

/-! # Hecke Euler phases under the relative idèle norm

The normalized order on the actual local norm multiplies by the residue degree.
This identifies the upstairs unramified local value for arbitrary Hecke characters. -/

public noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

namespace RiemannMasullo

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L]

private theorem valuation_eq_of_order_eq {v : HeightOneSpectrum (𝓞 K)}
    {x y : (v.adicCompletion K)ˣ}
    (h : (FiniteIdeleGroup.localOrder v x).toAdd = (FiniteIdeleGroup.localOrder v y).toAdd) :
    Valued.v x.val = Valued.v y.val := by
  rw [FiniteIdeleGroup.localOrder_apply, FiniteIdeleGroup.localOrder_apply, neg_inj] at h
  have hx : Valued.v x.val ≠ 0 := (map_ne_zero _).mpr x.ne_zero
  have hy : Valued.v y.val ≠ 0 := (map_ne_zero _).mpr y.ne_zero
  rw [← WithZero.exp_log hx, ← WithZero.exp_log hy, h]

/-- The chosen order-one element is a Mathlib valuation uniformizer in the same completion. -/
theorem chosenLocalOrderSection_one_isUniformizer (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v.IsUniformizer (FiniteIdeleGroup.chosenLocalOrderSection v 1).val := by
  let x := FiniteIdeleGroup.chosenLocalOrderSection v 1
  have h := FiniteIdeleGroup.localOrder_chosenLocalOrderSection v 1
  change (FiniteIdeleGroup.localOrder v x).toAdd = 1 at h
  rw [FiniteIdeleGroup.localOrder_apply] at h
  have hlog : WithZero.log (Valued.v x.val) = -1 := by omega
  have hx : Valued.v x.val ≠ 0 := (map_ne_zero _).mpr x.ne_zero
  have hv : Valued.v x.val = WithZero.exp (-1 : ℤ) := by
    rw [← WithZero.exp_log hx, hlog]
  exact hv.trans (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
    (v.valuedAdicCompletion_surjective K))).symm

private theorem restrict_onePlace (ν : HeckeCharacter (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    ν.restrict v x.val = ν (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x) := by
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  rfl

private theorem unramified_onePlace_eq_of_order_eq (ν : HeckeCharacter (𝓞 K) K)
    {v : HeightOneSpectrum (𝓞 K)} (hν : ν.IsUnramifiedAt v) {x y : (v.adicCompletion K)ˣ}
    (h : (FiniteIdeleGroup.localOrder v x).toAdd = (FiniteIdeleGroup.localOrder v y).toAdd) :
    ν (IdeleGroup.finitePlaceIdeleClass v x) = ν (IdeleGroup.finitePlaceIdeleClass v y) := by
  exact (restrict_onePlace ν v x).symm.trans ((hν.restrict_apply_eq (valuation_eq_of_order_eq h)).trans
    (restrict_onePlace ν v y))

/-- Unramified characters stay unramified after pullback by the actual relative norm.
The local Euler phase upstairs is the residue-degree power of the lower phase. -/
theorem heckeCharacter_normPullback_localValue (ν : HeckeCharacter (𝓞 K) K)
    (v : HeightOneSpectrum (𝓞 K)) (hν : ν.IsUnramifiedAt v)
    (W : {W : HeightOneSpectrum (𝓞 L) // _root_.finitePlaceBelow (K := K) W = v}) :
    let ψ : HeckeCharacter (𝓞 L) L := ν.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom K L)
    ψ.IsUnramifiedAt W.1 ∧ ψ.localValue W.1 = ν.localValue v ^ (W.1.asIdeal.inertiaDeg (𝓞 K)) := by
  let ψ : HeckeCharacter (𝓞 L) L := ν.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom K L)
  change ψ.IsUnramifiedAt W.1 ∧ ψ.localValue W.1 = _
  let : Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L v W).toAlgebra
  let n := LocalFieldTheory.normUnits (v.adicCompletion K) (W.1.adicCompletion L)
  have norm_apply (x : (W.1.adicCompletion L)ˣ) :
      ψ.restrict W.1 x.val = ν (IdeleGroup.finitePlaceIdeleClass v (n x)) := by
    rw [restrict_onePlace]
    exact congrArg ν (IdeleGroup.ideleClassNorm_finitePlaceIdeleClass_eq_normUnits
      (K := K) (L := L) v W x)
  have order_apply (x : (W.1.adicCompletion L)ˣ) :
      (FiniteIdeleGroup.localOrder v (n x)).toAdd =
       (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) * (FiniteIdeleGroup.localOrder W.1 x).toAdd :=
    FiniteIdeleGroup.localOrder_normUnits K L v W x
  have hψ : ψ.IsUnramifiedAt W.1 := by
    apply HeckeCharacter.isUnramifiedAt_iff.mpr
    intro u
    let x := Units.map (W.1.adicCompletionIntegers L).subtype.toMonoidHom u
    change ψ.restrict W.1 x.val = 1
    rw [norm_apply]
    have hx : (FiniteIdeleGroup.localOrder W.1 x).toAdd = 0 :=
      (FiniteIdeleGroup.localOrder_eq_zero_iff W.1 x).mpr ⟨u.val.property, u.inv.property⟩
    calc
      ν (IdeleGroup.finitePlaceIdeleClass v (n x)) = ν (IdeleGroup.finitePlaceIdeleClass v 1) := by
        apply unramified_onePlace_eq_of_order_eq ν hν
        simp [order_apply, hx]
      _ = 1 := by simp
  refine ⟨hψ, ?_⟩
  let π := FiniteIdeleGroup.chosenLocalOrderSection v 1
  let piUp := FiniteIdeleGroup.chosenLocalOrderSection W.1 1
  let f := W.1.asIdeal.inertiaDeg (𝓞 K)
  rw [hψ.localValue_eq piUp.val (chosenLocalOrderSection_one_isUniformizer W.1), norm_apply,
    hν.localValue_eq π.val (chosenLocalOrderSection_one_isUniformizer v), restrict_onePlace]
  calc
    ν (IdeleGroup.finitePlaceIdeleClass v (n piUp)) = ν (IdeleGroup.finitePlaceIdeleClass v (π ^ f)) := by
      apply unramified_onePlace_eq_of_order_eq ν hν
      rw [order_apply, map_pow]
      simp only [piUp, π, Int.toAdd_pow, FiniteIdeleGroup.localOrder_chosenLocalOrderSection, mul_one, one_mul, f]
    _ = _ := by rw [map_pow, map_pow]

/-- The project norm-twist phases of a unitary character and its norm lift satisfy the same formula. -/
theorem unitary_normPullback_localValue (ν : PontryaginDual (NumberField.IdeleClassGroup (𝓞 K) K))
    (v : HeightOneSpectrum (𝓞 K)) (hν : (ideleClassNormTwist ν 0).IsUnramifiedAt v)
    (W : {W : HeightOneSpectrum (𝓞 L) // _root_.finitePlaceBelow (K := K) W = v}) :
    let ψ := ν.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom K L)
    (ideleClassNormTwist ψ 0).IsUnramifiedAt W.1 ∧
      (ideleClassNormTwist ψ 0).localValue W.1 =
        (ideleClassNormTwist ν 0).localValue v ^ W.1.asIdeal.inertiaDeg (𝓞 K) := by
  let normMap := NumberField.IdeleClassGroup.normContinuousMonoidHom K L
  have he : ideleClassNormTwist (ν.comp normMap) 0 = (ideleClassNormTwist ν 0).comp normMap := by
    ext x
    change (ν (normMap x) : ℂ) * _ ^ (0 : ℂ) = (ν (normMap x) : ℂ) * _ ^ (0 : ℂ)
    simp
  change (ideleClassNormTwist (ν.comp normMap) 0).IsUnramifiedAt W.1 ∧ _
  rw [he]
  exact heckeCharacter_normPullback_localValue _ v hν W

end RiemannMasullo

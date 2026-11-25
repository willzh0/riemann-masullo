module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.UnramifiedPrimeArtin
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Ramification.FiniteRamifiedPrimes
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SUnit.Herbrand
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal

/-! # Frobenius order in the relative idèle class norm quotient

Nyll’s standard reciprocity sends the class of an order-one uniformizer at an
unramified place to its geometric Frobenius. Its order is the residue degree. -/

@[expose] public noncomputable section

open NumberField IsDedekindDomain
open GlobalClassFieldTheory GlobalClassFieldTheory.Reciprocity GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField

namespace RiemannMasullo

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L]

local notation "C[" F "]" => NumberField.IdeleClassGroup (𝓞 F) F
local notation "N" => NumberField.IdeleClassGroup.norm K L
local notation "place[" F "]" => HeightOneSpectrum (𝓞 F)

/-- The usual class of a chosen local uniformizer in the actual relative idèle norm quotient. -/
def relativeNormPrimeClass (v : place[K]) : C[K] ⧸ (N).range :=
  QuotientGroup.mk' (N).range (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v
    (FiniteIdeleGroup.chosenLocalOrderSection v 1))

section Abelian
variable [IsAbelianGalois K L]

/-- The standard reciprocity isomorphism evaluates any order-one one-place idèle at
the native prime Artin automorphism (geometric Frobenius in this convention). -/
theorem normResidue_of_onePlace_order_one (v : place[K])
    (hun : ChosenFinitePlaceIsUnramified (K := K) (L := L) v) (x : (v.adicCompletion K)ˣ)
    (hx : (FiniteIdeleGroup.localOrder v x).toAdd = 1) :
    standardNumberFieldNormResidueContinuousMulEquiv K L
        (QuotientGroup.mk' (N).range (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x)) =
      finitePlacePrimeArtin (K := K) (L := L) v := by
  change globalNormResidueMonoidHom K L (IdeleGroup.finitePlaceIdeleClass v x) = _
  have hlocal := DFunLike.congr_fun
    (globalNormResidueMonoidHom_comp_finitePlaceIdeleClass (K := K) (L := L) v) x
  refine hlocal.trans ?_
  rw [chosenFinitePlaceArtin_eq_primeArtin_zpow_of_chosenUnramified v hun x, hx, zpow_one]

/-- In the global norm quotient, the prime class has full local order at each unramified place. -/
theorem orderOf_relativeNormPrimeClass_eq_localDegree (v : place[K])
    (hun : ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    orderOf (relativeNormPrimeClass K L v) = finitePlaceLocalDegree (K := K) (L := L) v := by
  let e := standardNumberFieldNormResidueContinuousMulEquiv K L
  have he : e.toMulEquiv (relativeNormPrimeClass K L v) = finitePlacePrimeArtin (K := K) (L := L) v :=
    normResidue_of_onePlace_order_one K L v hun _ (FiniteIdeleGroup.localOrder_chosenLocalOrderSection v 1)
  rw [← e.toMulEquiv.orderOf_eq, he]
  exact orderOf_finitePlacePrimeArtin_eq_finitePlaceLocalDegree_of_chosenUnramified v hun

theorem relativeNormPrimeClass_eq_one_iff_split (v : place[K])
    (hun : ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    relativeNormPrimeClass K L v = 1 ↔ FinitePlaceSplitsCompletely (K := K) (L := L) v := by
  rw [← orderOf_eq_one_iff, orderOf_relativeNormPrimeClass_eq_localDegree K L v hun,
    finitePlaceSplitsCompletely_iff_localDegree_eq_one]

/-- Every upper prime has residue degree equal to the order of the standard lower
uniformizer in the global norm quotient, for every unramified base place. -/
theorem orderOf_relativeNormPrimeClass_eq_inertiaDeg (v : place[K])
    (hun : ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (W : {W : place[L] // _root_.finitePlaceBelow (K := K) W = v}) :
    orderOf (relativeNormPrimeClass K L v) = W.1.asIdeal.inertiaDeg (𝓞 K) := by
  let w := chosenFinitePlaceExtension (L := L) v
  let V := finitePlaceExtensionCentre (K := K) (L := L) v w
  let : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
  let : V.asIdeal.LiesOver v.asIdeal := finitePlaceExtensionCentre_liesOver (K := K) (L := L) v w
  let : W.1.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal W.2).symm⟩
  let : Algebra.IsUnramifiedAt (𝓞 K) V.asIdeal := isUnramifiedAt_of_chosenFinitePlaceIsUnramified v hun
  let := finitePlaceMulAction K L
  have hstab : finitePlaceDecompositionGroup (K := K) (L := L) v = MulAction.stabilizer Gal(L/K) V :=
    absoluteValueDecompositionGroup_eq_finitePlaceStabilizer (K := K) (L := L) v w
  rw [orderOf_relativeNormPrimeClass_eq_localDegree K L v hun, ← finitePlaceDecompositionGroup_card_eq_localDegree,
    hstab, finitePlace_stabilizer_card_eq_localDegree]
  change (V.asIdeal.under (𝓞 K)).ramificationIdxIn (𝓞 L) * (V.asIdeal.under (𝓞 K)).inertiaDegIn (𝓞 L) = _
  rw [← V.asIdeal.over_def v.asIdeal, Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal V.asIdeal Gal(L/K),
    Ideal.ramificationIdx_eq_one V.asIdeal (𝓞 K), one_mul, Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal W.1.asIdeal Gal(L/K)]

/-- A single finite exceptional set, consisting of the ramified base places, works
simultaneously for every place upstairs. -/
theorem exists_finset_orderOf_relativeNormPrimeClass_eq_inertiaDeg :
    ∃ S : Finset (place[K]), ∀ v ∉ S,
      ∀ W : {W : place[L] // _root_.finitePlaceBelow (K := K) W = v},
        orderOf (relativeNormPrimeClass K L v) = W.1.asIdeal.inertiaDeg (𝓞 K) := by
  classical
  let hfinite := AlgebraicNumberTheory.Ramification.finite_ramified_base_heightOne_primes (𝓞 K) (𝓞 L)
  refine ⟨hfinite.toFinset, fun v hv W ↦ orderOf_relativeNormPrimeClass_eq_inertiaDeg K L v ?_ W⟩
  let w := chosenFinitePlaceExtension (L := L) v
  apply chosenFinitePlaceIsUnramified_of_isUnramifiedAt
  by_contra hram
  exact hv (hfinite.mem_toFinset.mpr ⟨finitePlaceExtensionCentre (K := K) (L := L) v w,
    finitePlaceExtensionCentre_liesOver (K := K) (L := L) v w, hram⟩)

end Abelian

/-- In prime Galois degree, an unramified lower prime has either trivial norm
class and splits completely, or has norm class of the full extension degree. -/
theorem primeDegree_relativeNormPrimeClass_dichotomy [IsGalois K L]
    (hp : (Module.finrank K L).Prime) (v : place[K])
    (hun : ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    (FinitePlaceSplitsCompletely (K := K) (L := L) v ∧ relativeNormPrimeClass K L v = 1) ∨
      (¬ FinitePlaceSplitsCompletely (K := K) (L := L) v ∧
       orderOf (relativeNormPrimeClass K L v) = Module.finrank K L) := by
  let : Fact (Module.finrank K L).Prime := ⟨hp⟩
  let : IsCyclic Gal(L/K) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K L)
  let : IsAbelianGalois K L := IsAbelianGalois.of_isCyclic K L
  have hs := relativeNormPrimeClass_eq_one_iff_split K L v hun
  by_cases hv : FinitePlaceSplitsCompletely (K := K) (L := L) v
  · exact Or.inl ⟨hv, hs.mpr hv⟩
  refine Or.inr ⟨hv, ?_⟩
  have horder := orderOf_dvd_natCard (relativeNormPrimeClass K L v)
  rw [Nat.card_congr (standardNumberFieldNormResidueContinuousMulEquiv K L).toEquiv,
    IsGalois.card_aut_eq_finrank] at horder
  exact ((Nat.dvd_prime hp).mp horder).resolve_left (fun h ↦ hv (hs.mp (orderOf_eq_one_iff.mp h)))

end RiemannMasullo

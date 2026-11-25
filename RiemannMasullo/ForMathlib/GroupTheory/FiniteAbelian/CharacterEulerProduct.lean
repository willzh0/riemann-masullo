module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Topology.Algebra.Group.Quotient

/-! # Euler products over the unitary dual of a finite abelian group -/

@[expose] public noncomputable section

open Finset Polynomial Function

namespace RiemannMasullo

private theorem prod_one_sub_circleHom_generator {G : Type*} [CommGroup G] [Finite G]
    [Fintype (G →* Circle)] {x : G} (hx : ∀ g, g ∈ Subgroup.zpowers x) (X : ℂ) :
    (∏ θ : G →* Circle, (1 - X * (θ x : ℂ))) = 1 - X ^ Nat.card G := by
  classical
  let n := Nat.card G
  let S := nthRootsFinset n (1 : ℂ)
  let e₀ := (IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator hx Circle).trans
    (rootsOfUnityCircleEquiv n)
  let e₁ : {z : ℂ // z ∈ nthRoots n (1:ℂ)} ≃ {z : ℂ // z ∈ S} :=
    Equiv.subtypeEquivRight (fun _ ↦ by simp [S,nthRootsFinset])
  let e := e₀.toEquiv.trans ((rootsOfUnityEquivNthRoots ℂ n).trans e₁)
  have he (θ : G →* Circle) : (e θ).val = (θ x : ℂ) := by
    change ((rootsOfUnityCircleEquiv n
      (IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator hx Circle θ)).val : ℂ) = _
    rw [rootsOfUnityCircleEquiv_apply]
    rfl
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ n
  calc
    _ = ∏ z : S, (1 - X * (z : ℂ)) := Fintype.prod_equiv e _ _ (fun θ ↦ by rw [he])
    _ = ∏ z ∈ S, (1 - X * z) := by
      exact (Finset.prod_subtype S (fun _ ↦ Iff.rfl) (fun z : ℂ ↦ 1 - X * z)).symm
    _ = _ := by
      simpa only [one_pow, mul_comm X] using
        (hζ.pow_sub_pow_eq_prod_sub_mul (1:ℂ) X (Nat.card_pos (α := G))).symm

private theorem circleHom_card (G : Type*) [CommGroup G] [Finite G] :
    Nat.card (G →* Circle) = Nat.card G :=
  (Nat.card_congr MonoidHom.toHomUnitsMulEquiv.toEquiv).trans
    (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G Circle)

private theorem circleHom_finite (G : Type*) [CommGroup G] [Finite G] :
    Finite (G →* Circle) := Finite.of_equiv (G →* Circleˣ) MonoidHom.toHomUnitsMulEquiv.symm.toEquiv

/-- Evaluating every unitary character of a finite abelian group at `x` gives
the Euler polynomial for a regular permutation with cycles of length `orderOf x`. -/
theorem prod_one_sub_circleHom_apply {G : Type*} [CommGroup G] [Finite G]
    [Fintype (G →* Circle)] (x : G) (X : ℂ) :
    (∏ θ : G →* Circle, (1 - X * (θ x : ℂ))) =
      (1 - X ^ orderOf x) ^ (Nat.card G / orderOf x) := by
  classical
  let H := Subgroup.zpowers x
  let a : H := ⟨x, Subgroup.mem_zpowers x⟩
  have ha (u : H) : u ∈ Subgroup.zpowers a := by
    obtain ⟨m,hm⟩ := (Subgroup.mem_zpowers_iff.mp u.property)
    exact ⟨m, Subtype.ext hm⟩
  let : Finite (H →* Circle) := circleHom_finite H
  let : Fintype (H →* Circle) := Fintype.ofFinite _
  let r := MonoidHom.domRestrictHom H Circle
  have hs : Surjective r := by
    intro χ
    obtain ⟨ψ, hψ⟩ := MonoidHom.domRestrict_surjective (M := Circle) H χ.toHomUnits
    exact ⟨(Units.coeHom Circle).comp ψ, MonoidHom.ext fun u ↦
      congrArg Units.val (DFunLike.congr_fun hψ u)⟩
  have hk : Nat.card r.ker = Nat.card G / orderOf x := by
    calc
      _ = Nat.card (G ⧸ H →* Circle) :=
        Nat.card_congr (MonoidHom.domRestrictHomKerEquiv Circle H).toEquiv
      _ = Nat.card (G ⧸ H) := circleHom_card _
      _ = _ := by rw [← H.index_eq_card, H.index_eq_card_div, Nat.card_zpowers]
  have hf (χ : H →* Circle) :
      Fintype.card {θ : G →* Circle // r θ = χ} = Nat.card G / orderOf x :=
    Fintype.card_eq_nat_card.trans <|
      (Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hs χ)).trans hk
  let q (χ : H →* Circle) := 1 - X * (χ a : ℂ)
  calc
    _ = ∏ θ, q (r θ) := rfl
    _ = ∏ χ, ∏ _θ : {θ // r θ = χ}, q χ := (Fintype.prod_fiberwise' r q).symm
    _ = ∏ χ : H →* Circle, q χ ^ (Nat.card G / orderOf x) := by
      simp only [prod_const, card_univ, hf]
    _ = (∏ χ : H →* Circle, q χ) ^ (Nat.card G / orderOf x) := Finset.prod_pow _ _ _
    _ = _ := by rw [show (∏ χ : H →* Circle, q χ) = 1 - X ^ Nat.card H from
        prod_one_sub_circleHom_generator ha X, Nat.card_zpowers]

section Pullback

variable {A B : Type*} [CommGroup A] [CommGroup B] [TopologicalSpace A] [TopologicalSpace B]

/-- Characters that become trivial after pullback are exactly the characters of
the algebraic quotient when the quotient topology is discrete. -/
noncomputable def pullbackKernelEquivQuotientCircleHom (N : A →ₜ* B)
    [DiscreteTopology (B ⧸ N.toMonoidHom.range)] :
    (PontryaginDual.map N).toMonoidHom.ker ≃ ((B ⧸ N.toMonoidHom.range) →* Circle) where
  toFun θ := QuotientGroup.lift _ θ.val.toMonoidHom (by
    rintro y ⟨a,rfl⟩
    exact DFunLike.congr_fun (MonoidHom.mem_ker.mp θ.property) a)
  invFun ψ := ⟨⟨ψ.comp (QuotientGroup.mk' N.toMonoidHom.range),
      (show Continuous ψ from continuous_of_discreteTopology).comp QuotientGroup.continuous_mk⟩, by
    apply MonoidHom.mem_ker.mpr
    apply PontryaginDual.ext
    intro a
    change ψ (QuotientGroup.mk (N a)) = 1
    rw [(QuotientGroup.eq_one_iff _).mpr (show N a ∈ N.toMonoidHom.range from ⟨a,rfl⟩),map_one]⟩
  left_inv _ := Subtype.ext (PontryaginDual.ext fun _ ↦ rfl)
  right_inv ψ := MonoidHom.ext (fun q ↦ QuotientGroup.induction_on q (fun _ ↦ rfl))

/-- The same product on an actual indexed pullback kernel. The element in the exponent
is the image in the range quotient, with its true order. -/
theorem prod_one_sub_pullbackKernel_apply (N : A →ₜ* B)
    [Finite (B ⧸ N.toMonoidHom.range)] [DiscreteTopology (B ⧸ N.toMonoidHom.range)]
    {ι : Type*} [Fintype ι] (e : ι ≃ (PontryaginDual.map N).toMonoidHom.ker) (g : B) (X : ℂ) :
    let q : B ⧸ N.toMonoidHom.range := (QuotientGroup.mk' _) g
    (∏ i, (1 - X * ((e i).val g : ℂ))) =
      (1 - X ^ orderOf q) ^ (Nat.card (B ⧸ N.toMonoidHom.range) / orderOf q) := by
  let d := e.trans (pullbackKernelEquivQuotientCircleHom N)
  let : Fintype ((B ⧸ N.toMonoidHom.range) →* Circle) := Fintype.ofEquiv ι d
  let q := (QuotientGroup.mk' N.toMonoidHom.range) g
  calc
    _ = ∏ θ : (B ⧸ N.toMonoidHom.range) →* Circle, (1 - X * (θ q : ℂ)) :=
      Fintype.prod_equiv d _ _ (fun _ ↦ rfl)
    _ = _ := prod_one_sub_circleHom_apply q X

end Pullback

end RiemannMasullo

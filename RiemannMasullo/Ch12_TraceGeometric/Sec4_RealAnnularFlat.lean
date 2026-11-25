module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Bounds

/-!
# The even flat outputs for a real annular cutoff

Theorem 12.4.1.1, pp. 514–517. In the rational model with the real place alone,
a positive inner cutoff lets the powers in the even Fourier expansion take
values in the flat Schwartz space. The fixed-cutoff construction is due to
dyknapp, issue #7354.
-/

public noncomputable section

namespace RiemannMasullo

open Bornology Filter Function Set Topology
open scoped ContDiff

/-- Every fixed-order derivative of the normalized powers is bounded uniformly in
the exponent on the support interval. -/
private theorem realAnnularFlatPowers_monomial_bound
    (A : ℝ) (hA : 0 < A) (m j : ℕ) (x : ℝ) (hx : |x| ≤ A) :
    ‖iteratedFDeriv ℝ j (fun y : ℝ ↦ (y / (2 * A)) ^ m) x‖ ≤
      (j.factorial : ℝ) * A⁻¹ ^ j := by
  have hscale : (fun y : ℝ ↦ (y / (2 * A)) ^ m) =
      fun y : ℝ ↦ ((2 : ℝ)⁻¹) ^ m * (A⁻¹ * y) ^ m := by
    funext y
    rw [← mul_pow]
    congr 1
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  have hmon : ContDiff ℝ j (fun y : ℝ ↦ y ^ m) := contDiff_id.pow m
  have hxA : |A⁻¹ * x| ≤ 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hA)]
    calc
      _ ≤ A⁻¹ * A := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hA.le)
      _ = 1 := inv_mul_cancel₀ hA.ne'
  have hchoose : (m.choose j : ℝ) ≤ (2 : ℝ) ^ m := by
    exact_mod_cast Nat.choose_le_two_pow m j
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hscale, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul hmon]
  simp only [iteratedDeriv_pow]
  rw [Real.norm_eq_abs,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  simp only [abs_mul, abs_pow, abs_of_nonneg (inv_nonneg.mpr hA.le), Nat.abs_cast,
    abs_of_pos (inv_pos.mpr (by norm_num : (0 : ℝ) < 2))]
  have hxA' : A⁻¹ * |x| ≤ 1 := by
    simpa only [abs_mul, abs_of_nonneg (inv_nonneg.mpr hA.le)] using hxA
  calc
    _ ≤ ((2 : ℝ)⁻¹) ^ m *
        (A⁻¹ ^ j * ((j.factorial : ℝ) * (2 : ℝ) ^ m * 1)) := by
          gcongr
          exact pow_le_one₀ (mul_nonneg (inv_nonneg.mpr hA.le) (abs_nonneg _)) hxA'
    _ = _ := by
      rw [inv_pow]
      field_simp

/-- Paper: Step II, pp. 516–517, and footnote 2, p. 514.
A smooth mask supported on a bounded annulus times the normalized even
monomials forms a bounded family in the flat Schwartz space. -/
theorem exists_realAnnularFlatPowers (ρ : ℝ → ℂ) (A : ℝ) (hA : 0 < A)
    (hρ : ContDiff ℝ ∞ ρ) (hK : tsupport ρ ⊆ Icc (-A) A)
    (h0 : ∀ᶠ x in 𝓝 (0 : ℝ), ρ x = 0) :
    ∃ u : ℕ → ↥realSchwartzFlatAtOrigin,
      (∀ n x, (u n).val x = ρ x * ((x / (2 * A) : ℝ) : ℂ) ^ (2 * n)) ∧
      IsVonNBounded ℂ (range u) := by
  let p (n : ℕ) (x : ℝ) : ℝ := (x / (2 * A)) ^ (2 * n)
  have hp (n : ℕ) : ContDiff ℝ ∞ (p n) := (contDiff_id.div_const _).pow _
  have hc : HasCompactSupport ρ := isCompact_Icc.of_isClosed_subset isClosed_closure hK
  let r : SchwartzMap ℝ ℂ := hc.toSchwartzMap hρ
  let v (n : ℕ) : SchwartzMap ℝ ℂ :=
    (hc.smul_left (f := p n)).toSchwartzMap ((hp n).smul hρ)
  have hv (n : ℕ) : v n ∈ realSchwartzFlatAtOrigin := by
    apply (mem_realSchwartzFlatAtOrigin_iff _).mpr
    intro j
    have hz : (v n : ℝ → ℂ) =ᶠ[𝓝 0] fun _ ↦ 0 :=
      h0.mono fun x hx ↦ by change p n x • ρ x = 0; rw [hx, smul_zero]
    rw [hz.iteratedDeriv_eq]
    simp
  let u (n : ℕ) : ↥realSchwartzFlatAtOrigin := ⟨v n, hv n⟩
  refine ⟨u, ?_, ?_⟩
  · intro n x
    change p n x • ρ x = _
    simp [p, Complex.real_smul, mul_comm]
  · have hw := LinearMap.withSeminorms_induced (schwartz_withSeminorms ℂ ℝ ℂ)
        realSchwartzFlatAtOrigin.subtype
    apply hw.isVonNBounded_iff_seminorm_bddAbove.mpr
    rintro ⟨k, j⟩
    let C := ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ((i.factorial : ℝ) * A⁻¹ ^ i) * SchwartzMap.seminorm ℂ 0 (j - i) r
    have hC : 0 ≤ C := by
      apply Finset.sum_nonneg
      intro i _
      have := apply_nonneg (SchwartzMap.seminorm ℂ 0 (j - i)) r
      positivity
    refine ⟨A ^ k * C, ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    change SchwartzMap.seminorm ℂ k j (v n) ≤ _
    apply SchwartzMap.seminorm_le_bound ℂ k j _ (mul_nonneg (pow_nonneg hA.le _) hC)
    intro x
    change ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (fun y ↦ p n y • ρ y) x‖ ≤ _
    by_cases hx : x ∈ tsupport ρ
    · have hxa := abs_le.mpr (hK hx)
      have hd : ‖iteratedFDeriv ℝ j (fun y ↦ p n y • ρ y) x‖ ≤ C := by
        apply (norm_iteratedFDeriv_smul_le (hp n) hρ x (by simp)).trans
        apply Finset.sum_le_sum
        intro i _
        have hpi := realAnnularFlatPowers_monomial_bound A hA (2 * n) i x hxa
        have hri := SchwartzMap.norm_iteratedFDeriv_le_seminorm (𝕜 := ℂ) r (j - i) x
        gcongr
        exact hri
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (by simpa using hxa) k)
        hd (norm_nonneg _) (pow_nonneg hA.le k)
    · have hz : iteratedFDeriv ℝ j (fun y ↦ p n y • ρ y) x = 0 := by
        by_contra hn
        exact hx (tsupport_smul_subset_right (p n) ρ (support_iteratedFDeriv_subset j hn))
      rw [hz, norm_zero, mul_zero]
      exact mul_nonneg (pow_nonneg hA.le _) hC

/-- Paper: Step II, pp. 516–517, and footnote 2, p. 514.
On an even annular mask the bounded flat outputs are even, with exactly the
mask's topological support at every index. -/
theorem exists_even_realAnnularFlatPowers (ρ : ℝ → ℂ) (A : ℝ) (hA : 0 < A)
    (hρ : ContDiff ℝ ∞ ρ) (hK : tsupport ρ ⊆ Icc (-A) A)
    (h0 : ∀ᶠ x in 𝓝 (0 : ℝ), ρ x = 0) (he : Function.Even ρ) :
    ∃ u : ℕ → ↥realSchwartzFlatAtOrigin,
      (∀ n x, (u n).val x = ρ x * ((x / (2 * A) : ℝ) : ℂ) ^ (2 * n)) ∧
      IsVonNBounded ℂ (range u) ∧
      ∀ n, Function.Even ((u n).val : ℝ → ℂ) ∧ tsupport ((u n).val : ℝ → ℂ) = tsupport ρ := by
  obtain ⟨u, hu, hb⟩ := exists_realAnnularFlatPowers ρ A hA hρ hK h0
  refine ⟨u, hu, hb, fun n ↦ ⟨?_, ?_⟩⟩
  · intro x
    simp only [hu, he x, neg_div, Complex.ofReal_neg, even_two, Even.mul_right, Even.neg_pow]
  · apply congrArg closure
    ext x
    change (u n).val x ≠ 0 ↔ ρ x ≠ 0
    rw [hu, mul_ne_zero_iff]
    refine ⟨And.left, fun hx ↦ ⟨hx, pow_ne_zero _ ?_⟩⟩
    have hx' : x ≠ 0 := fun e ↦ hx (e ▸ h0.self_of_nhds)
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero hx' (mul_ne_zero (by norm_num) hA.ne'))

end RiemannMasullo

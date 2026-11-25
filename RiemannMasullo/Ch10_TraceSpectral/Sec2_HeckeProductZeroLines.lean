module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.Ch06_LocalGlobal.Sec3_HeckeProductMultiplicities

/-! Bounded-height representatives for finite products of Hecke functions. -/

@[expose] public noncomputable section

open Set NumberField
open scoped BigOperators NumberField.AdeleRing

namespace RiemannMasullo

section HeckeProductZeroLines

set_option quotPrecheck false
local notation "U(" F ")" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "mult(" χ "," z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat
local notation "site(" σ "," t ")" => ((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "rightStrip" => Ioo (1 / 2 : ℝ) 1
local notation "representatives(" χ ")" =>
  ∃ T : ℝ, ∀ σ t : ℝ, σ ∈ rightStrip → 1 < mult(χ,site(σ,t)) →
    ∃ u : ℝ, |u| ≤ T ∧ 1 < mult(χ,site(σ,u))
local notation "HP" => {z : ℂ // 1 < z.re}

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
Reconstruction: The bounded-height assertion for a
single completed Hecke row is equivalent to finiteness of its multiple-zero abscissae
in the open right half-strip. -/
theorem spectralStripJet_boundedHeight_iff_finite_multiple_zero_abscissae (χ : U(F)) :
    representatives(χ) ↔
      {σ : ℝ | σ ∈ rightStrip ∧ ∃ t : ℝ, 1 < mult(χ,site(σ,t))}.Finite := by
  classical
  constructor
  · rintro ⟨T, hT⟩
    apply (spectralStripJet_multiple_zero_lines_finite_on_compact χ T).subset
    rintro σ ⟨hs, t, ht⟩
    exact ⟨⟨hs.1.le, hs.2.le⟩, hT σ t hs ht⟩
  · intro hS
    let S := {σ : ℝ | σ ∈ rightStrip ∧ ∃ t : ℝ, 1 < mult(χ,site(σ,t))}
    have hfin : S.Finite := hS
    choose u hu using fun σ : S ↦ σ.property.2
    let := hfin.fintype
    obtain ⟨T, hT⟩ := (finite_range (fun σ : S ↦ |u σ|)).bddAbove
    refine ⟨T, fun σ t hs ht ↦ ?_⟩
    let p : S := ⟨σ, hs, t, ht⟩
    exact ⟨u p, hT (mem_range_self p), hu p⟩

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
Reconstruction: Replacing one unitary extension
by the chosen basepoint in its norm-one component preserves bounded-height
representability. The ordinates translate by a single real number. -/
theorem spectralStripJet_boundedHeight_iff_at_basepoint
    (χ : U(F)) (base : PontryaginDual (ideleClassNorm F).ker → U(F))
    (hbase : IsSpectralBasepointChoice base) :
    representatives(χ) ↔ representatives(base (χ.comp
      (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F))) := by
  obtain ⟨d, hd, _⟩ := hbase.existsUnique_ordinate_shift χ
  rw [spectralStripJet_boundedHeight_iff_finite_multiple_zero_abscissae,
    spectralStripJet_boundedHeight_iff_finite_multiple_zero_abscissae]
  apply Iff.of_eq
  congr 1
  ext σ
  constructor <;> rintro ⟨hs, t, ht⟩
  · refine ⟨hs, t + d, ?_⟩
    rw [Complex.ofReal_add, ← (hd σ t).2]
    exact ht
  · refine ⟨hs, t - d, ?_⟩
    rw [(hd σ (t - d)).2]
    simpa using ht

private theorem sum_gt_one_iff_multiple_or_common {ι : Type*} [Fintype ι] (n : ι → ℕ) :
    1 < ∑ i, n i ↔ (∃ i, 1 < n i) ∨ ∃ i j, i ≠ j ∧ 0 < n i ∧ 0 < n j := by
  classical
  constructor
  · intro h
    by_cases big : ∃ i, 1 < n i
    · exact Or.inl big
    · right
      obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ Nat.zero_le (n i))).mp
        (show 0 < ∑ i, n i by omega)
      have hni := (not_exists.mp big) i
      have hsplit := Finset.add_sum_erase Finset.univ n (Finset.mem_univ i)
      have hrest : 0 < ∑ j ∈ Finset.univ.erase i, n j := by omega
      obtain ⟨j, hj, hjpos⟩ := (Finset.sum_pos_iff_of_nonneg
        (fun j _ ↦ Nat.zero_le (n j))).mp hrest
      exact ⟨i, j, (Finset.mem_erase.mp hj).1.symm, hi, hjpos⟩
  · rintro (⟨i, hi⟩ | ⟨i, j, hij, hi, hj⟩)
    · exact hi.trans_le (Finset.single_le_sum (fun k _ ↦ Nat.zero_le (n k)) (Finset.mem_univ i))
    · have hle : n j ≤ ∑ k ∈ Finset.univ.erase i, n k :=
        Finset.single_le_sum (fun k _ ↦ Nat.zero_le (n k)) (Finset.mem_erase.mpr ⟨hij.symm, by simp⟩)
      have hsplit := Finset.add_sum_erase Finset.univ n (Finset.mem_univ i)
      omega

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
Reconstruction: For a finite Euler product of lower
Hecke rows, the abscissae to control come from a multiple lower root or two
distinct factors vanishing at the same complex point. -/
theorem spectralStripJet_boundedHeight_iff_of_finiteHeckeL_eq_prod {ι : Type*} [Fintype ι]
    (χ : U(F)) (ψ : ι → U(E))
    (hEuler : ∀ s : HP, finiteHeckeL χ s = ∏ i, finiteHeckeL (ψ i) s) :
    representatives(χ) ↔ {σ : ℝ | σ ∈ rightStrip ∧ ∃ t : ℝ,
      (∃ i, 1 < mult(ψ i,site(σ,t))) ∨
        ∃ i j, i ≠ j ∧ 0 < mult(ψ i,site(σ,t)) ∧ 0 < mult(ψ j,site(σ,t))}.Finite := by
  rw [spectralStripJet_boundedHeight_iff_finite_multiple_zero_abscissae]
  simp_rw [spectralZeroMultiplicity_eq_sum_of_finiteHeckeL_eq χ ψ hEuler,
    sum_gt_one_iff_multiple_or_common]

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
Reconstruction: If an arithmetic identity gives
a common multiplicity factor greater than one, all positive lower orders, including
simple ones, are exactly the sites contributing multiple-zero lines upstairs. -/
theorem spectralStripJet_boundedHeight_iff_of_multiplicity_eq_mul_sum {ι : Type*} [Fintype ι]
    (χ : U(F)) (ψ : ι → U(E)) (h : ℕ) (hh : 1 < h)
    (hmul : ∀ z : ℂ, mult(χ,z) = h * ∑ i, mult(ψ i,z)) :
    representatives(χ) ↔ {σ : ℝ | σ ∈ rightStrip ∧ ∃ t : ℝ, ∃ i,
      0 < mult(ψ i,site(σ,t))}.Finite := by
  have hroot (z : ℂ) : 1 < mult(χ,z) ↔ ∃ i, 0 < mult(ψ i,z) := by
    rw [hmul z]
    have hpos : 0 < ∑ i, mult(ψ i,z) ↔ ∃ i, 0 < mult(ψ i,z) := by
      simpa using (Finset.sum_pos_iff_of_nonneg (s := Finset.univ)
        (fun i _ ↦ Nat.zero_le (mult(ψ i,z))))
    rw [← hpos]
    constructor
    · intro hp
      by_contra! hn
      rw [Nat.le_zero.mp hn, Nat.mul_zero] at hp
      omega
    · exact fun hp ↦ hh.trans_le (Nat.le_mul_of_pos_right h hp)
  rw [spectralStripJet_boundedHeight_iff_finite_multiple_zero_abscissae]
  simp_rw [hroot]

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
Reconstruction: For a literal power of a finite
Euler product with exponent greater than one, the bounded-height condition is
equivalent to finiteness of the abscissae of all the lower rows' right-half zeros. -/
theorem spectralStripJet_boundedHeight_iff_of_finiteHeckeL_eq_prod_pow {ι : Type*} [Fintype ι]
    (χ : U(F)) (ψ : ι → U(E)) (h : ℕ) (hh : 1 < h)
    (hEuler : ∀ s : HP, finiteHeckeL χ s = (∏ i, finiteHeckeL (ψ i) s) ^ h) :
    representatives(χ) ↔ {σ : ℝ | σ ∈ rightStrip ∧ ∃ t : ℝ, ∃ i,
      0 < mult(ψ i,site(σ,t))}.Finite := by
  apply spectralStripJet_boundedHeight_iff_of_multiplicity_eq_mul_sum χ ψ h hh
  have he (s : HP) : finiteHeckeL χ s = ∏ p : Fin h × ι, finiteHeckeL (ψ p.2) s := by
    simpa [Fintype.prod_prod_type] using hEuler s
  intro z
  simpa [Fintype.sum_prod_type] using
    spectralZeroMultiplicity_eq_sum_of_finiteHeckeL_eq χ (fun p : Fin h × ι ↦ ψ p.2) he z

end HeckeProductZeroLines

end RiemannMasullo

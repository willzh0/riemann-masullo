module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasulloClassField.AbelianHeckeMultiplicities
public import RiemannMasulloClassField.CyclicNormDescent
import Mathlib.FieldTheory.PrimitiveElement

/-! # Cyclic descent for the uniform multiplicity bound

Proposition 10.2.2.2, pp. 446–447, leads the project to ask for a single integer bounding
the multiplicities of all unitary Hecke characters of each fixed field (#7220).
The statements here reduce that assertion to characters with trivial rational stabilizer
on the fields reachable by prime-degree Galois descent. Class field theory yields
norm descent and the Euler factorization. The finite recursion preserves the total
field degree and the multiplicity function at every complex point. -/

@[expose] public noncomputable section

open Function NumberField Set IsDedekindDomain
open scoped NumberField.AdeleRing

namespace RiemannMasullo.Isolated.CyclicMultiplicity

set_option quotPrecheck false

universe u

local notation "C[" K "]" => IdeleClassGroup (𝓞 K) K
local notation "U[" K "]" => PontryaginDual (C[K])
local notation "m(" ψ ", " z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL ψ) z).untop₀.toNat

/-- One prime-degree Galois descent from a number field. -/
abbrev Step (F : Type u) [Field F] [NumberField F] :=
  {E : IntermediateField ℚ F // IsGalois E F ∧ Nat.Prime (Module.finrank E F)}

/-- A field reached by a finite (possibly empty) sequence of prime-degree Galois descents.
The ambient field need not be Galois over the final subfield. -/
inductive Below (F : Type u) [Field F] [NumberField F] :
    (E : Type u) → [Field E] → [NumberField E] → Prop where
  | root : Below F F
  | step {K : Type u} [Field K] [NumberField K] (h : Below F K) (e : Step K) :
    Below F e.val

variable {F : Type u} [Field F] [NumberField F]

/-- Triviality of the stabilizer of a unitary character under the action of the rational
field automorphisms on idèle classes. -/
def TrivialStabilizer (ψ : U[F]) : Prop :=
  ∀ σ : F ≃ₐ[ℚ] F, ψ.comp (IdeleClassGroup.congrContinuousMulEquiv σ) = ψ → σ = 1

private theorem step_degree_lt (e : Step F) : Module.finrank ℚ e.val < Module.finrank ℚ F := by
  rw [← Module.finrank_mul_finrank ℚ e.val F]
  simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left e.property.2.one_lt
    (Module.finrank_pos : 0 < Module.finrank ℚ e.val)

/-- A choice of spectral charts realizes precisely the bound on the genuine
multiplicities of *all* unitary characters, including arbitrary imaginary norm twists. -/
theorem chartBound_iff {χ : PontryaginDual (ideleClassNorm F).ker → U[F]}
    (hχ : IsSpectralBasepointChoice (F := F) χ) (M : ℕ) :
    (∀ (ω : PontryaginDual (ideleClassNorm F).ker) (b t : ℝ), m(χ ω, (b : ℂ) + (t : ℂ) * Complex.I) ≤ M) ↔
      ∀ (ψ : U[F]) (z : ℂ), m(ψ, z) ≤ M := by
  constructor
  · intro h ψ z
    obtain ⟨d, hd, _⟩ := IsSpectralBasepointChoice.existsUnique_ordinate_shift
      (F := F) (χ := χ) hχ ψ
    let r : (ideleClassNorm F).ker →ₜ* C[F] :=
      ⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩
    have hb := h (ψ.comp r) z.re (z.im + d)
    have he := (hd z.re z.im).2
    exact (congrArg (fun w : ℂ ↦ m(ψ, w)) (Complex.re_add_im z).symm).le.trans
      (he.le.trans (by simpa only [Complex.ofReal_add] using hb))
  · exact fun h ω b t ↦ h (χ ω) ((b : ℂ) + (t : ℂ) * Complex.I)

local notation "N(" K ", " e ")" => IdeleClassGroup.normContinuousMonoidHom (e : Step K).val K

/-- Enumerate all characters trivial on the actual relative norm, once each. -/
def normTwists (e : Step F) :
    Fin (Module.finrank e.val F) ≃ (PontryaginDual.map N(F, e)).toMonoidHom.ker := by
  let : IsGalois e.val F := e.property.1
  exact (primeDegree_ideleClass_normTwist_indexing e.val F e.property.2).choose

/-- The orders of the norm pullback add at every complex point, including repeated
zeros of distinct twists. -/
theorem normPullback_multiplicity (e : Step F) (ν : U[e.val]) (z : ℂ) :
    m(ν.comp N(F, e), z) = ∑ i, m(ν * (normTwists e i).val, z) := by
  let : IsGalois e.val F := e.property.1
  let : Fact (Module.finrank e.val F).Prime := ⟨e.property.2⟩
  let : IsCyclic Gal(F/e.val) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank e.val F)
  let : IsAbelianGalois e.val F := IsAbelianGalois.of_isCyclic e.val F
  exact abelian_normPullback_multiplicity (normTwists e) ν z

/-- Every lower-field multiplicity is bounded by that of its own norm pullback at the
same point. In particular, a field's multiplicity bound passes to each cyclic subfield. -/
theorem multiplicity_le_normPullback (e : Step F) (ν : U[e.val]) (z : ℂ) :
    m(ν, z) ≤ m(ν.comp N(F, e), z) := by
  obtain ⟨j, hj⟩ := (normTwists e).surjective 1
  have hj' : (normTwists e j).val = 1 := congrArg Subtype.val hj
  calc
    m(ν, z) = m(ν * (normTwists e j).val, z) := by rw [hj', mul_one]
    _ ≤ ∑ i, m(ν * (normTwists e i).val, z) :=
      Finset.single_le_sum (f := fun i ↦ m(ν * (normTwists e i).val, z))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    _ = m(ν.comp N(F, e), z) := (normPullback_multiplicity e ν z).symm

private theorem bound_below {M : ℕ} (hF : ∀ (ψ : U[F]) (z : ℂ), m(ψ, z) ≤ M)
    {K : Type u} [Field K] [NumberField K] (hK : Below F K) :
    ∀ (ν : U[K]) (z : ℂ), m(ν, z) ≤ M := by
  induction hK with
  | root => exact hF
  | step _ e ih =>
    exact fun ν z ↦ (multiplicity_le_normPullback e ν z).trans (ih _ _)

private theorem bound_from_leaves
    (hleaf : ∀ (K : Type u) [Field K] [NumberField K], Below F K →
      ∃ M : ℕ, ∀ (ψ : U[K]), TrivialStabilizer ψ → ∀ z : ℂ, m(ψ, z) ≤ M)
    (n : ℕ) : ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
       Below F K → ∃ M : ℕ, ∀ (ψ : U[K]) (z : ℂ), m(ψ, z) ≤ M := by
  classical
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro K _ _ hdegree hK
    obtain ⟨M, hM⟩ := hleaf K hK
    have hsub (e : Step K) : ∃ B : ℕ, ∀ (ν : U[e.val]) (z : ℂ), m(ν, z) ≤ B :=
      ih _ (hdegree ▸ step_degree_lt e) e.val rfl (.step hK e)
    choose B hB using hsub
    let : Finite (IntermediateField ℚ K) :=
      Field.finite_intermediateField_of_exists_primitive_element ℚ K (Field.exists_primitive_element ℚ K)
    obtain ⟨D, hD⟩ := Finite.bddAbove_range (fun e : Step K ↦ Module.finrank e.val K * B e)
    refine ⟨max M D, fun ψ z ↦ ?_⟩
    by_cases hψ : TrivialStabilizer ψ
    · exact le_max_of_le_left (hM ψ hψ z)
    obtain ⟨e, ν, rfl⟩ := exists_primeDegree_norm_descent_of_nontrivial_stabilizer K ψ hψ
    calc
      m(ν.comp N(K, e), z) = ∑ i, m(ν * (normTwists e i).val, z) :=
        normPullback_multiplicity e ν z
      _ ≤ ∑ _i : Fin (Module.finrank e.val K), B e :=
        Finset.sum_le_sum (fun i _ ↦ hB e _ _)
      _ = Module.finrank e.val K * B e := by simp
      _ ≤ D := hD ⟨e, rfl⟩
      _ ≤ max M D := le_max_right _ _

/-- The field-wise multiplicity assertion of #7220 is equivalent to a bound, for each
reachable cyclic-tower subfield, on only its characters with trivial rational stabilizer.
Each subfield has its own bound, uniform over its characters and ordinates. -/
theorem chartBound_iff_orbitFree_below
    {χ : PontryaginDual (ideleClassNorm F).ker → U[F]} (hχ : IsSpectralBasepointChoice (F := F) χ) :
    (∃ M : ℕ, ∀ (ω : PontryaginDual (ideleClassNorm F).ker) (b t : ℝ), m(χ ω, (b : ℂ) + (t : ℂ) * Complex.I) ≤ M) ↔
      ∀ (K : Type u) [Field K] [NumberField K], Below F K →
        ∃ M : ℕ, ∀ (ψ : U[K]), TrivialStabilizer ψ → ∀ z : ℂ, m(ψ, z) ≤ M := by
  constructor
  · rintro ⟨M, hM⟩ K _ _ hK
    exact ⟨M, fun ψ _ ↦ bound_below ((chartBound_iff hχ M).mp hM) hK ψ⟩
  · intro h
    obtain ⟨M, hM⟩ := bound_from_leaves h _ F rfl .root
    exact ⟨M, (chartBound_iff hχ M).mpr hM⟩

private theorem multiset_sum_values {α ι : Type*} [Fintype ι]
    (v : α → ℕ) (l : ι → Multiset α) :
    ((∑ j, l j).map v).sum = ∑ j, ((l j).map v).sum := by
  let a : Multiset α →+ ℕ :=
    { toFun := fun s ↦ (s.map v).sum
      map_zero' := by simp
      map_add' := fun s t ↦ by simp }
  exact map_sum a l Finset.univ

/-- The zero-multiplicity functions in a finite factorization are independent of height.
Each entry records the absolute degree and the full multiplicity function of one terminal
unitary Hecke character. Repetitions count with their multiplicity. -/
theorem exists_orbitFree_decomposition (ψ : U[F]) :
    ∃ l : Multiset (ℕ × (ℂ → ℕ)),
      (∀ a ∈ l, ∃ (K : Type u) (_ : Field K) (_ : NumberField K) (ν : U[K]),
        Below F K ∧ TrivialStabilizer ν ∧
          a = (Module.finrank ℚ K, fun z ↦ m(ν, z))) ∧
      (l.map Prod.fst).sum = Module.finrank ℚ F ∧
      ∀ z : ℂ, (l.map (fun a ↦ a.2 z)).sum = m(ψ, z) := by
  classical
  let Leaf (a : ℕ × (ℂ → ℕ)) := ∃ (K : Type u) (_ : Field K) (_ : NumberField K) (ν : U[K]),
    Below F K ∧ TrivialStabilizer ν ∧ a = (Module.finrank ℚ K, fun z ↦ m(ν, z))
  have go (n : ℕ) : ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
      Below F K → ∀ χ : U[K], ∃ l : Multiset (ℕ × (ℂ → ℕ)), (∀ a ∈ l, Leaf a) ∧
        (l.map Prod.fst).sum = Module.finrank ℚ K ∧
        ∀ z, (l.map (fun a ↦ a.2 z)).sum = m(χ, z) := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro K _ _ hdegree hK χ
      by_cases hχ : TrivialStabilizer χ
      · refine ⟨{(Module.finrank ℚ K, fun z ↦ m(χ, z))}, ?_, by simp, fun z ↦ by simp⟩
        intro a ha
        exact ⟨K, _, _, χ, hK, hχ, Multiset.mem_singleton.mp ha⟩
      obtain ⟨e, ν, rfl⟩ := exists_primeDegree_norm_descent_of_nontrivial_stabilizer K χ hχ
      have sub (i : Fin (Module.finrank e.val K)) :=
        ih _ (hdegree ▸ step_degree_lt e) e.val rfl (.step hK e) (ν * (normTwists e i).val)
      choose l hleaf hsum horders using sub
      refine ⟨∑ i, l i, ?_, ?_, fun z ↦ ?_⟩
      · intro a ha
        obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp ha
        exact hleaf i a hi
      · rw [multiset_sum_values]
        simp only [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        rw [Nat.mul_comm, Module.finrank_mul_finrank]
      · rw [multiset_sum_values, normPullback_multiplicity e ν z]
        exact Finset.sum_congr rfl (fun i _ ↦ horders i z)
  exact go _ F rfl .root ψ

/-- Any upper bound on multiplicity divided by the field degree propagates with
the same constant. The hypothesis and conclusion are pointwise at the same ordinate. -/
theorem multiplicity_mul_le_of_orbitFree_below
    (ψ : U[F]) (z : ℂ) (a b : ℕ)
    (h : ∀ (K : Type u) [Field K] [NumberField K], Below F K →
      ∀ (ν : U[K]), TrivialStabilizer ν →
        m(ν, z) * b ≤ a * Module.finrank ℚ K) :
    m(ψ, z) * b ≤ a * Module.finrank ℚ F := by
  obtain ⟨l, hleaf, hdeg, horder⟩ := exists_orbitFree_decomposition ψ
  have hvalue (v : ℕ × (ℂ → ℕ)) (hv : v ∈ l) : v.2 z * b ≤ a * v.1 := by
    obtain ⟨K, _, _, ν, hK, hν, rfl⟩ := hleaf v hv
    exact h K hK ν hν
  have hl := Multiset.sum_map_le_sum_map (s := l) (fun v ↦ v.2 z * b) (fun v ↦ a * v.1) hvalue
  rwa [Multiset.sum_map_mul_right, Multiset.sum_map_mul_left, hdeg, horder] at hl

/-- The global field-wise assertion of #7220 only requires fields' stabilizer-free
unitary characters. The uniform integer on either side is allowed to depend on the field. -/
theorem all_chartBounds_iff_orbitFree :
    (∀ (K : Type u) [Field K] [NumberField K]
      (χ : PontryaginDual (ideleClassNorm K).ker → U[K]), IsSpectralBasepointChoice (F := K) χ →
        ∃ M : ℕ, ∀ (ω : PontryaginDual (ideleClassNorm K).ker) (b t : ℝ),
          m(χ ω, (b : ℂ) + (t : ℂ) * Complex.I) ≤ M) ↔
      ∀ (K : Type u) [Field K] [NumberField K], ∃ M : ℕ,
        ∀ (ψ : U[K]), TrivialStabilizer ψ → ∀ z : ℂ, m(ψ, z) ≤ M := by
  constructor
  · intro h K _ _
    obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice K
    obtain ⟨M, hM⟩ := h K χ hχ
    exact ⟨M, fun ψ _ ↦ (chartBound_iff hχ M).mp hM ψ⟩
  · intro h K _ _ χ hχ
    exact (chartBound_iff_orbitFree_below hχ).mpr
      (fun E _ _ _ ↦ h E)

end RiemannMasullo.Isolated.CyclicMultiplicity

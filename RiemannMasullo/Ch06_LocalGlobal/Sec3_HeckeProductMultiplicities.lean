module

public import RiemannMasullo.Ch03_IdelicZeta.Sec2
public import RiemannMasullo.Ch06_LocalGlobal.Sec3

/-! # Finite Hecke products and completed zero multiplicities

A product identity for unitary characters on the Euler half-plane gives addition of the
positive orders of their completed continuations at every point. Separate finite Euler
deletions are allowed. In particular, the local identity can be verified over the
finite places of the base field outside a finite set. -/
@[expose] public noncomputable section

open Filter Function Set IsDedekindDomain NumberField
open scoped Topology BigOperators NumberField.AdeleRing

namespace RiemannMasullo

section HeckeMultiplicities
set_option quotPrecheck false

local notation "U(" F ")" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "ord(" χ "," z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "mult(" χ "," z ")" => (ord(χ,z)).untop₀.toNat
local notation "R(" S "," χ "," z ")" => (∏ v ∈ (S : Finset _), (finiteHeckeEulerFactor χ v z)⁻¹)
local notation "HP" => {z : ℂ // 1 < z.re}

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

private theorem reciprocal_finiteEuler_analytic (χ : U(F)) (v : V(F)) :
    Differentiable ℂ (fun z ↦ (finiteHeckeEulerFactor χ v z)⁻¹) := by
  classical
  by_cases h : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · simp only [finiteHeckeEulerFactor, h, ite_true, inv_inv]
    have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
    exact (differentiable_const _).sub <| (differentiable_const _).mul
      ((differentiable_id.neg).const_cpow (.inl hq))
  · simp [finiteHeckeEulerFactor, h]

private theorem reciprocal_finiteEuler_ne_zero (χ : U(F)) (v : V(F)) {z : ℂ} (hz : 0 < z.re) :
    (finiteHeckeEulerFactor χ v z)⁻¹ ≠ 0 := by
  classical
  by_cases h : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · simp only [finiteHeckeEulerFactor, h, ite_true, inv_inv]
    have hq : (1 : ℝ) < v.asIdeal.absNorm := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hlt : ‖(ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ)^(-z)‖ < 1 := by
      rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq), Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
    intro he
    exact hlt.ne (by rw [← sub_eq_zero.mp he, norm_one])
  · simp [finiteHeckeEulerFactor, h]

private theorem completed_order_ne_top (χ : U(F)) (z : ℂ) : ord(χ,z) ≠ ⊤ := by
  let s : HP := ⟨2, by norm_num⟩
  have h := continuedCompletedHeckeL_spec χ
  have he : continuedCompletedHeckeL χ s ≠ 0 := by
    rw [h.2 s]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans s.property))
      (finiteHeckeL_ne_zero_of_one_lt_re χ s)
  have h0 := (h.1 (mem_univ s.val)).meromorphicOrderAt_eq_zero_iff.mpr he
  apply h.1.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ s.val) (mem_univ z)
  rw [h0]
  exact WithTop.zero_ne_top

private theorem completed_order_nonneg (χ : U(F)) {z : ℂ} (hz₀ : 0 < z.re) (hz₁ : z.re < 1) :
    0 ≤ ord(χ,z) := by
  have h := continuedCompletedHeckeL_spec χ
  by_cases ht : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨t, ⟨_,_,_,han⟩, _⟩ := completedHeckeL_continuation_simplePoles χ _ h.1 h.2 ht
    apply (han z ?_).meromorphicOrderAt_nonneg
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor <;> intro he <;> have hh := congrArg Complex.re he <;>
      simp [Complex.mul_re] at hh <;> linarith
  · exact ((completedHeckeL_continuation_entire χ _ h.1 h.2 ht).analyticAt z).meromorphicOrderAt_nonneg

private theorem multiplicity_eq_zero_outside_openStrip (χ : U(F)) (z : ℂ)
    (hz : ¬ (0 < z.re ∧ z.re < 1)) : mult(χ,z) = 0 := by
  have hzero : ¬ 0 < ord(χ,z) := by
    intro ho
    apply hz
    have hr : 0 < z.re := by
      by_contra! hneg
      have h := continuedCompletedHeckeL_spec χ
      have h' := continuedCompletedHeckeL_spec χ⁻¹
      obtain ⟨ε,hε,hn,he⟩ := completedHeckeL_continuation_functionalEquation χ _ _
        h.1 h.2 h'.1 h'.2
      let r (s : ℂ) := 1 - s
      have hd : HasDerivAt r (-1) z := (hasDerivAt_id z).const_sub 1
      have hrord := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹)
        (show AnalyticAt ℂ r z by dsimp [r]; fun_prop) (hd.deriv.trans_ne (by norm_num))
      rw [show continuedCompletedHeckeL χ⁻¹ ∘ r = ε * continuedCompletedHeckeL χ from funext he,
        meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z) (hn z)] at hrord
      have ho' : 0 < ord(χ⁻¹,1-z) := hrord ▸ ho
      have hpos : 0 < (1-z).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
      have hlt := completedHeckeL_continuation_zeros χ⁻¹ _ h'.1 h'.2 hpos ho'
      simp only [Complex.sub_re, Complex.one_re] at hlt
      linarith
    exact ⟨hr, completedHeckeL_continuation_zeros χ _ (continuedCompletedHeckeL_spec χ).1
      (continuedCompletedHeckeL_spec χ).2 hr ho⟩
  generalize ord(χ,z) = o at *
  cases o with
  | top => simp
  | coe k =>
    simp only [WithTop.untop₀_coe]
    exact Int.toNat_eq_zero.mpr (by exact_mod_cast not_lt.mp hzero)

private def correctedFinitePart (χ : U(F)) (S : Finset V(F)) (z : ℂ) : ℂ :=
  (R(S,χ,z) * (heckeGammaFactor χ z)⁻¹) * continuedCompletedHeckeL χ z

private theorem correctedFinitePart_unit (χ : U(F)) (S : Finset V(F)) :
    Differentiable ℂ (fun z ↦ R(S,χ,z) * (heckeGammaFactor χ z)⁻¹) :=
  (Differentiable.fun_finsetProd (fun i _ ↦ reciprocal_finiteEuler_analytic χ i)).mul
    (differentiable_inv_heckeGammaFactor χ)

private theorem correctedFinitePart_meromorphic (χ : U(F)) (S : Finset V(F)) :
    MeromorphicOn (correctedFinitePart χ S) univ := fun z _ ↦
  ((correctedFinitePart_unit χ S).analyticAt z).meromorphicAt.mul
    ((continuedCompletedHeckeL_spec χ).1.meromorphicOn z (mem_univ _))

private theorem correctedFinitePart_order (χ : U(F)) (S : Finset V(F)) {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt (correctedFinitePart χ S) z = ord(χ,z) :=
  meromorphicOrderAt_mul_of_ne_zero ((correctedFinitePart_unit χ S).analyticAt z)
    (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ ↦ reciprocal_finiteEuler_ne_zero χ v hz)
      (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hz)))

private theorem correctedFinitePart_euler (χ : U(F)) (S : Finset V(F)) (s : HP) :
    correctedFinitePart χ S s = R(S,χ,s) * finiteHeckeL χ s := by
  unfold correctedFinitePart
  rw [(continuedCompletedHeckeL_spec χ).2 s]
  change _ * ((heckeGammaFactor χ s) * finiteHeckeL χ s) = _
  rw [mul_assoc, ← mul_assoc ((heckeGammaFactor χ s)⁻¹),
    inv_mul_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans s.property)), one_mul]

private theorem natOrder_sum {ι : Type*} (S : Finset ι) (o : ι → WithTop ℤ)
    (h : ∀ i, 0 ≤ o i) (ht : ∀ i, o i ≠ ⊤) :
    (∑ i ∈ S, o i).untop₀.toNat = ∑ i ∈ S, (o i).untop₀.toNat := by
  have lift (i : ι) : o i = ↑(((o i).untop₀.toNat : ℕ) : ℤ) := by
    obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp (ht i)
    have hh := h i
    rw [← he] at *
    have he0 : 0 ≤ e := by exact_mod_cast hh
    simp [Int.toNat_of_nonneg he0]
  have hs : (∑ i ∈ S, o i) = ↑(((∑ i ∈ S, (o i).untop₀.toNat) : ℕ) : ℤ) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ ↦ lift i
  rw [hs, WithTop.untop₀_coe, Int.toNat_natCast]

/-- The Chapter 10 multiplicities of a finite Hecke factorization add at every complex
point. Finitely many finite Euler factors on each side may be removed independently. -/
theorem spectralZeroMultiplicity_eq_sum_of_imprimitiveHeckeL_eq {ι : Type*} [Fintype ι]
    (χ : U(F)) (ψ : ι → U(E)) (S : Finset V(F)) (T : ι → Finset V(E))
    (hEuler : ∀ s : HP, R(S,χ,s) * finiteHeckeL χ s =
      ∏ i, (R(T i,ψ i,s) * finiteHeckeL (ψ i) s)) (z : ℂ) :
    mult(χ,z) = ∑ i, mult(ψ i,z) := by
  by_cases hz : 0 < z.re ∧ z.re < 1
  · let f := correctedFinitePart χ S
    let p (w : ℂ) := ∏ i, correctedFinitePart (ψ i) (T i) w
    have hm : MeromorphicOn (f-p) univ :=
      (correctedFinitePart_meromorphic χ S).sub (fun w _ ↦
        MeromorphicAt.fun_prod fun i _ ↦ correctedFinitePart_meromorphic (ψ i) (T i) w (mem_univ _))
    have h2 : meromorphicOrderAt (f-p) (2:ℂ) = ⊤ := by
      apply meromorphicOrderAt_eq_top_iff.mpr
      have hN : ∀ᶠ w in 𝓝 (2:ℂ), 1 < w.re :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
      filter_upwards [hN.filter_mono nhdsWithin_le_nhds] with w hw
      apply sub_eq_zero.mpr
      let t : HP := ⟨w,hw⟩
      change correctedFinitePart χ S t.val = ∏ i, correctedFinitePart (ψ i) (T i) t.val
      simp only [correctedFinitePart_euler]
      exact hEuler t
    have heq := (meromorphicOrderAt_eq_top_iff.mp
      (hm.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
        (mem_univ 2) (mem_univ z) h2)).mono (fun w hw ↦ sub_eq_zero.mp hw)
    have ho := meromorphicOrderAt_congr (f₁ := f) (f₂ := p) heq
    rw [show meromorphicOrderAt f z = ord(χ,z) from correctedFinitePart_order χ S hz.1,
      show meromorphicOrderAt p z = ∑ i, meromorphicOrderAt (correctedFinitePart (ψ i) (T i)) z from
        meromorphicOrderAt_fun_prod (fun i _ ↦ correctedFinitePart_meromorphic (ψ i) (T i) z (mem_univ _))] at ho
    simp_rw [correctedFinitePart_order _ _ hz.1] at ho
    rw [ho, natOrder_sum _ _ (fun i ↦ completed_order_nonneg (ψ i) hz.1 hz.2)
      (fun i ↦ completed_order_ne_top (ψ i) z)]
  · simp [multiplicity_eq_zero_outside_openStrip _ _ hz]

/-- All finite Euler factors included. No equality of completed products, conductor
factors or archimedean gamma factors is required. -/
theorem spectralZeroMultiplicity_eq_sum_of_finiteHeckeL_eq {ι : Type*} [Fintype ι]
    (χ : U(F)) (ψ : ι → U(E)) (hEuler : ∀ s : HP, finiteHeckeL χ s = ∏ i, finiteHeckeL (ψ i) s)
    (z : ℂ) : mult(χ,z) = ∑ i, mult(ψ i,z) :=
  spectralZeroMultiplicity_eq_sum_of_imprimitiveHeckeL_eq χ ψ ∅ (fun _ ↦ ∅)
    (fun s ↦ by simpa only [Finset.prod_empty, one_mul] using hEuler s) z

open Classical in
/-- Delete the Euler factors in a finite set of places. The resulting family has the
ordinary finite Hecke value multiplied by the reciprocal of the omitted factors. -/
theorem finiteHeckeL_omitting_hasProd (χ : U(F)) (S : Finset V(F)) (s : HP) :
    HasProd (fun v ↦ if v ∈ S then 1 else finiteHeckeEulerFactor χ v s)
      (R(S,χ,s) * finiteHeckeL χ s) := by
  classical
  let c (v : V(F)) := if v ∈ S then (finiteHeckeEulerFactor χ v s)⁻¹ else 1
  have h : HasProd c (R(S,χ,s)) := by
    have he : ∏ v ∈ S, c v = R(S,χ,s) :=
      Finset.prod_congr rfl (fun v hv ↦ by simp [c,hv])
    rw [← he]
    exact hasProd_prod_of_ne_finset_one (fun v hv ↦ by simp [c,hv])
  apply (h.mul (finiteHeckeL_hasProd χ s)).congr_fun
  intro v
  by_cases hv : v ∈ S
  · have hn : finiteHeckeEulerFactor χ v s ≠ 0 :=
      by simpa only [ne_eq, inv_eq_zero] using
           (reciprocal_finiteEuler_ne_zero χ v (zero_lt_one.trans s.property))
    simp [c,hv,hn]
  · simp [c,hv]

/-- There are only finitely many upper finite places restricting to a prescribed
finite place of a subfield. -/
theorem finite_places_over_finite [Algebra E F] (v : V(E)) :
    Set.Finite {w : V(F) | w.under (𝓞 E) = v} := by
  let f : {w : V(F) // w.under (𝓞 E) = v} → v.asIdeal.primesOver (𝓞 F) :=
    fun w ↦ ⟨w.val.asIdeal,w.val.isPrime,⟨(congrArg HeightOneSpectrum.asIdeal w.property).symm⟩⟩
  have hi : Injective f := fun x y h ↦ Subtype.ext
    (HeightOneSpectrum.ext (congrArg Subtype.val h))
  exact @Set.toFinite _ _ (Finite.of_injective f hi)


/-- An equality of the local Euler factors at every place, with the upper primes
grouped by their actual restriction, gives the primitive finite Hecke identity
throughout the Euler half-plane. -/
theorem finiteHeckeL_eq_prod_of_localEulerFactors [Algebra E F] {ι : Type*} [Fintype ι]
    (χ : U(F)) (ψ : ι → U(E))
    (hlocal : ∀ (v : V(E)) (s : HP),
      (∏' w : {w : V(F) // w.under (𝓞 E) = v}, finiteHeckeEulerFactor χ w.val s) =
        ∏ i, finiteHeckeEulerFactor (ψ i) v s)
    (s : HP) : finiteHeckeL χ s = ∏ i, finiteHeckeL (ψ i) s := by
  let d : V(F) → V(E) := HeightOneSpectrum.under (𝓞 E)
  let e := Equiv.sigmaFiberEquiv d
  have hu : HasProd (fun x ↦ finiteHeckeEulerFactor χ (e x) s) (finiteHeckeL χ s) :=
    e.hasProd_iff.mpr (finiteHeckeL_hasProd χ s)
  have hd : HasProd (fun v ↦ ∏ i, finiteHeckeEulerFactor (ψ i) v s) (∏ i, finiteHeckeL (ψ i) s) :=
    hasProd_prod fun i _ ↦ finiteHeckeL_hasProd (ψ i) s
  apply (hu.sigma ?_).unique hd
  intro v
  let : Fintype {w : V(F) // d w = v} := (finite_places_over_finite (F := F) v).fintype
  rw [← hlocal v s, tprod_fintype]
  exact hasProd_fintype _

/-- It suffices to compare the ordinary Euler factors above each prime outside a
finite exceptional set of the base field. The product indexed by the primes above
a given prime is finite. The exceptional set may depend on the characters. -/
theorem spectralZeroMultiplicity_eq_sum_of_localEulerFactors_off_finset
    [Algebra E F] {ι : Type*} [Fintype ι] (χ : U(F)) (ψ : ι → U(E)) (B : Finset V(E))
    (hlocal : ∀ (v : V(E)), v ∉ B → ∀ s : HP,
      (∏' w : {w : V(F) // w.under (𝓞 E) = v}, finiteHeckeEulerFactor χ w.val s) =
        ∏ i, finiteHeckeEulerFactor (ψ i) v s)
    (z : ℂ) : mult(χ,z) = ∑ i, mult(ψ i,z) := by
  classical
  let d : V(F) → V(E) := HeightOneSpectrum.under (𝓞 E)
  let S := B.biUnion fun v ↦ (finite_places_over_finite (F := F) v).toFinset
  have hS (w : V(F)) : w ∈ S ↔ d w ∈ B := by
    simp [S,d]
  apply spectralZeroMultiplicity_eq_sum_of_imprimitiveHeckeL_eq χ ψ S (fun _ ↦ B)
  intro s
  let P (w : V(F)) : ℂ := if w ∈ S then 1 else finiteHeckeEulerFactor χ w s
  let Q (i : ι) (v : V(E)) : ℂ := if v ∈ B then 1 else finiteHeckeEulerFactor (ψ i) v s
  have hp : HasProd P (R(S,χ,s) * finiteHeckeL χ s) := finiteHeckeL_omitting_hasProd χ S s
  have hq : HasProd (fun v ↦ ∏ i, Q i v) (∏ i, R(B,ψ i,s) * finiteHeckeL (ψ i) s) :=
    hasProd_prod fun i _ ↦ finiteHeckeL_omitting_hasProd (ψ i) B s
  let e := Equiv.sigmaFiberEquiv d
  have hgroup : HasProd (fun x ↦ P (e x)) (R(S,χ,s) * finiteHeckeL χ s) :=
    e.hasProd_iff.mpr hp
  apply (hgroup.sigma ?_).unique hq
  intro v
  let : Fintype {w : V(F) // d w = v} := (finite_places_over_finite (F := F) v).fintype
  change HasProd (fun w : {w : V(F) // d w = v} ↦ P w.val) (∏ i, Q i v)
  by_cases hv : v ∈ B
  · have ht (w : {w : V(F) // d w = v}) : w.val ∈ S := (hS _).mpr (w.property.symm ▸ hv)
    simpa only [P, Q, hv, ht, ite_true, Finset.prod_const_one] using
      (hasProd_one (β := {w : V(F) // d w = v}) (α := ℂ))
  · have ht (w : {w : V(F) // d w = v}) : w.val ∉ S :=
      fun he ↦ hv (w.property ▸ (hS _).mp he)
    simp only [P,Q,hv,ht,ite_false]
    rw [← hlocal v hv s, tprod_fintype]
    exact hasProd_fintype _


end HeckeMultiplicities
end RiemannMasullo

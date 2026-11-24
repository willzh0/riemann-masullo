module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Quantitative placement of a sharp frequency cutoff between finitely many sites. -/

public section

namespace SharpWindows

private theorem exists_clear_grid_point (s : Finset ℝ) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ i : Fin (s.card + 1), ∀ x ∈ s, r ≤ |a + (2 * (i.val : ℝ) + 1) * r - x| := by
  classical
  by_contra! h
  choose x hx hclose using h
  let f : Fin (s.card + 1) → ↥s := fun i ↦ ⟨x i, hx i⟩
  have distinct {i j : Fin (s.card + 1)} (hij : i < j) : f i ≠ f j := by
    intro heq
    have hxij : x i = x j := congrArg Subtype.val heq
    have hstep : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast (show i.val + 1 ≤ j.val from hij)
    have hi := (abs_lt.mp (hclose i)).1
    have hj := (abs_lt.mp (hclose j)).2
    rw [hxij] at hi
    nlinarith [mul_nonneg (sub_nonneg.mpr hstep) hr.le]
  have hinj : Function.Injective f := by
    intro i j heq
    rcases lt_trichotomy i j with h | h | h
    · exact (distinct h heq).elim
    · exact h
    · exact (distinct h heq.symm).elim
  have hc := Fintype.card_le_of_injective f hinj
  simp at hc

/-- A cutoff can be kept away from all sites of an arbitrary divisor by a distance
depending only on the width and the number of sites in the interval. -/
theorem exists_cutoff_clearance (T : Set ℝ) (s : Finset ℝ) {a b : ℝ} (hab : a < b)
    (hs : ∀ x ∈ T, x ∈ Set.Icc a b → x ∈ s) :
    let r := (b - a) / (2 * ((s.card : ℝ) + 1))
    ∃ c : ℝ, a + r ≤ c ∧ c ≤ b - r ∧ ∀ x ∈ T, r ≤ |c - x| := by
  let r := (b - a) / (2 * ((s.card : ℝ) + 1))
  change ∃ c : ℝ, a + r ≤ c ∧ c ≤ b - r ∧ _
  have hr : 0 < r := div_pos (sub_pos.mpr hab) (by positivity)
  have hmul : r * (2 * ((s.card : ℝ) + 1)) = b - a :=
    div_mul_cancel₀ _ (by positivity)
  obtain ⟨i, hi⟩ := exists_clear_grid_point s a hr
  let c := a + (2 * (i.val : ℝ) + 1) * r
  have hlower : a + r ≤ c := by
    dsimp [c]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) i.val) hr.le]
  have hindex : (i.val : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hupper : c ≤ b - r := by
    dsimp [c]
    nlinarith [mul_nonneg (sub_nonneg.mpr hindex) hr.le]
  refine ⟨c, hlower, hupper, fun x hx ↦ ?_⟩
  by_cases left : a ≤ x
  · by_cases right : x ≤ b
    · exact hi x (hs x hx ⟨left, right⟩)
    · exact le_trans (by linarith : r ≤ -(c - x)) (neg_le_abs _)
  · exact le_trans (by linarith : r ≤ c - x) (le_abs_self _)

end SharpWindows

#print axioms SharpWindows.exists_cutoff_clearance

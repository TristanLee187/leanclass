import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Mathlib.Tactic.Set
import Library.Tactic.ExistsDelaborator
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Mathlib.Tactic.GCongr
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

set_option push_neg.use_distrib true
open Function

/- 2 points -/
theorem problem4a : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  push_neg
  use (fun x ↦ x)
  dsimp [Surjective]
  push_neg
  constructor
  · intros b; use b; simp
  · use 1
    intros a
    have ha := le_or_succ_le a 0
    obtain ha | ha := ha
    · apply ne_of_lt
      calc
        2 * a ≤ 2 * 0 := by rel [ha]
        _ = 0 := by ring
        _ < 1 := by numbers
    · apply ne_of_gt
      calc
        1 < 2 * 1 := by ring
        _ ≤ 2 * a := by rel [ha]

/- 2 points -/
theorem problem4b : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  dsimp [Surjective]; push_neg; use 0, 1; intros a; simp

/- 3 points -/
theorem problem4c {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  dsimp [Injective]
  intros a b h1
  have H := lt_trichotomy a b
  obtain H | H | H := H
  · have hfab := hf a b H
    have contra := ne_of_lt hfab
    contradiction
  · apply H
  · have hfba := hf b a H
    have contra := Ne.symm (ne_of_lt hfba)
    contradiction

/- 3 points -/
theorem problem4d {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp [Surjective]
  intros b
  simple_induction b with n IH
  · use x0; apply h0
  · obtain ⟨a,IH⟩ := IH
    use i a
    rw [hi,IH]

/- 2 points -/
theorem problem5a : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  constructor
  · intros a b h1
    dsimp at h1
    have h2 : 3 * a = 3 * b := by addarith [h1]
    cancel 3 at h2
  · intros y
    use ((4 - y)/3)
    dsimp
    ring

/- 2 points -/
theorem problem5b : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  dsimp [Bijective]; push_neg; left; dsimp [Injective]; push_neg
  use 0, -2
  simp; ring

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x - 1)/5

/- 3 points -/
theorem problem5c : Inverse u v := by
  constructor <;> (dsimp [u,v]; funext x; simp; ring)

/- 3 points -/
theorem problem5d {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  intros a b hfg
  apply hf; apply hg; apply hfg

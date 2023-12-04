import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Theory.InjectiveSurjective
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
import Library.Tactic.Product

set_option push_neg.use_distrib true
open Function

/- 3 points -/
theorem problem4a {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  intros b
  dsimp [Surjective] at *
  have hg' := hg b
  obtain ⟨c,hg'⟩ := hg'
  have hf' := hf c
  obtain ⟨d,hf'⟩ := hf'
  use d; rw [hf',hg']

/- 2 points -/
theorem problem4b {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  dsimp [Surjective] at *
  choose g hg using hf
  use g
  funext x
  simp
  apply hg

/- 2 points -/
theorem problem4c {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  dsimp [Inverse] at *
  obtain ⟨h1,h2⟩ := h
  constructor
  · apply h2
  · apply h1

/- 3 points -/
theorem problem4d {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  dsimp [Inverse] at *
  obtain ⟨h11,h12⟩ := h1
  obtain ⟨h21,h22⟩ := h2
  calc
    g1 = g1 ∘ id := by simp
    _ = g1 ∘ (f ∘ g2) := by rw [h22]
    _ = (g1 ∘ f) ∘ g2 := by rw [Function.comp.assoc]
    _ = id ∘ g2 := by rw [h11]
    _ = g2 := by simp

/- 1 points -/
theorem problem5a1 : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Injective]
  push_neg
  use (1,0), (3,1)
  constructor <;> simp

/- 1 points -/
theorem problem5a2 : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Surjective]
  intros b
  use (b+1,0)
  dsimp
  ring

/- 2 points -/
theorem problem5b : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intros a
  apply ne_of_gt
  calc
    -1 < 0 := by numbers
    _ ≤ a.fst ^ 2 + a.snd ^ 2 := by extra

/- 3 points -/
theorem problem5c : ¬ Injective
    (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  dsimp [Injective]
  push_neg
  use (0,0,0), (1,-2,1)
  constructor
  · ring
  · numbers

/- 3 points -/
theorem problem5d : Injective (fun ((x, y) : ℝ × ℝ) ↦ (x + y, x + 2 * y, x + 3 * y)) := by
  dsimp [Injective]
  intros x y H
  obtain ⟨H1, H2, H3⟩ := H
  have h2 : x.snd = y.snd :=
    calc
      x.snd = x.snd + (x.fst + x.snd) - (x.fst + x.snd) := by ring
      _ = (x.fst + 2 * x.snd) - (x.fst + x.snd) := by ring
      _ = (y.fst + 2 * y.snd) - (y.fst + y.snd) := by rw [H2,H1]
      _ = y.snd := by ring
  have h1 : x.fst = y.fst :=
    calc
      x.fst = x.fst + x.snd - x.snd := by ring
      _ = y.fst + y.snd - y.snd := by rw [H1,h2]
      _ = y.fst := by ring
  constructor
  · apply h1
  · apply h2

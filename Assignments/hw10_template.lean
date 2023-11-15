import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Theory.Comparison
import Library.Theory.Prime
import Mathlib.Tactic.Set
import Mathlib.Tactic.IntervalCases
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use
import Mathlib.Tactic.GCongr
import Library.Tactic.Cancel

def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d

termination_by _ n d hd => 2 * n - d

def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if 0 < - n then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1

/- 5 points -/
theorem problem4a (n : ℤ) : T n = n ^ 2 := by
  sorry

/- 5 points -/
theorem problem4b (a b : ℤ) (h : 0 < b) : ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  sorry

def gcd (a b : ℤ) : ℤ :=
  if 0 < b then
    gcd b (fmod a b)
  else if b < 0 then
    gcd b (fmod a (-b))
  else if 0 ≤ a then
    a
  else
    -a
termination_by _ a b => b

/- 5 points -/
theorem problem5a (a b : ℤ) : gcd a b ∣ b ∧ gcd a b ∣ a := by
  rw [gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · -- case `0 < b`
    have IH : _ ∧ _ := problem5a b (fmod a b) -- inductive hypothesis
    obtain ⟨IH_right, IH_left⟩ := IH
    constructor
    · -- prove that `gcd a b ∣ b`
      sorry
    · -- prove that `gcd a b ∣ a`
      sorry
  · -- case `b < 0`
    have IH : _ ∧ _ := problem5a b (fmod a (-b)) -- inductive hypothesis
    obtain ⟨IH_right, IH_left⟩ := IH
    constructor
    · -- prove that `gcd a b ∣ b`
      sorry
    · -- prove that `gcd a b ∣ a`
      sorry
  · -- case `b = 0`, `0 ≤ a`
    constructor
    · -- prove that `gcd a b ∣ b`
      sorry
    · -- prove that `gcd a b ∣ a`
      sorry
  · -- case `b = 0`, `a < 0`
    constructor
    · -- prove that `gcd a b ∣ b`
      sorry
    · -- prove that `gcd a b ∣ a`
      sorry
termination_by problem5a a b => b

mutual

def L (a b : ℤ) : ℤ :=
  if 0 < b then
    R b (fmod a b)
  else if b < 0 then
    R b (fmod a (-b))
  else if 0 ≤ a then
    1
  else
    -1

def R (a b : ℤ) : ℤ :=
  if 0 < b then
    L b (fmod a b) - (fdiv a b) * R b (fmod a b)
  else if b < 0 then
    L b (fmod a (-b)) + (fdiv a (-b)) * R b (fmod a (-b))
  else
    0

end
termination_by L a b => b ; R a b => b

#eval L (-21) 15 -- infoview displays `2`
#eval R (-21) 15 -- infoview displays `3`

#eval L 7 5 -- infoview displays `-2`
#eval R 7 5 -- infoview displays `3`
#eval gcd 7 5 -- infoview displays `1`

/- 5 points -/
theorem problem5b {d a b : ℤ} (ha : d ∣ a) (hb : d ∣ b) : d ∣ gcd a b := by
  sorry

import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Theory.Comparison
import Library.Theory.Prime
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use
import Mathlib.Tactic.GCongr
import Library.Tactic.Cancel

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

/- 2 points -/
theorem problem4a (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with n IH
  · rw [B]; simp
  · rw [B]; rw [IH]; ring

def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

/- 3 points -/
theorem problem4b (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with n IH
  · rw [S]; simp; numbers
  · rw [S]; rw [IH]; simp; ring

/- 3 points -/
theorem problem4c (n : ℕ) : S n ≤ 2 := by
  rw [problem4b]; simp

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

/- 3 points -/
theorem problem4d (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  simple_induction n with n IH
  · simp
  · rw [factorial]
    have hn : n + 2 > n + 1 := by addarith
    calc
      (n + 1 + 1) ^ (n + 1) = (n + 2) ^ (n + 1) := by ring
      _ = (n + 2) * (n + 2) ^ n := by ring
      _ ≥ (n + 2) * (n + 1) ^ n := by rel [hn]
      _ ≥ (n + 2) * (n + 1)! := by rel [IH]

def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

/- 3 points -/
theorem problem5a (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with n IH1 IH2
  · simp
  · simp
  · rw [q,IH1,IH2]; ring

def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

/- 3 points -/
theorem problem5b : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  use 7
  intros n h7
  two_step_induction_from_starting_point n, h7 with n hn IH1 IH2
  · simp
  · simp
  · rw [r]
    calc
      2 * r (n + 1) + r n ≥ 2 * 2 ^ (n + 1) + r n := by rel [IH2]
      _ ≥ 2 * 2 ^ (n + 1) + 2 ^ n := by rel [IH1]
      _ = 2 ^ (n + 2) + 2 ^ n := by ring
      _ ≥ 2 ^ (n + 2) := by extra

/- 3 points -/
theorem problem5c (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain nEven | nOdd := Nat.even_or_odd n
  · dsimp [Even] at nEven
    obtain ⟨m,nEven⟩ := nEven
    have hm : 2 * 0 < 2 * m :=
    calc
      2 * 0 = 0 := by ring
      _ < n := by rel [hn]
      _ = 2 * m := by rw [nEven]
    cancel 2 at hm
    have IH := problem5c m hm
    obtain ⟨a,x,IH1,IH2⟩ := IH
    use a + 1, x
    constructor
    · apply IH1
    · rw [nEven]
      calc
        2 * m = 2 * (2 ^ a * x) := by rw [IH2]
        _ = 2 ^ (a + 1) * x := by ring
  · use 0, n; simp; apply nOdd

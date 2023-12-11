import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Set
import Library.Theory.Comparison
import Library.Theory.InjectiveSurjective
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Define
import Library.Tactic.ExistsDelaborator
import Library.Tactic.Extra
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Product
import Library.Tactic.Rel
import Library.Tactic.Use

set_option push_neg.use_distrib true
open Set

notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)

/- 3 points -/
theorem problem4a : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  simp; use 5; simp

/- 3 points -/
theorem problem4b : {k : ℤ | 7 ∣ 9 * k} = {l : ℤ | 7 ∣ l} := by
  ext n
  dsimp
  constructor
  · intros H
    dsimp [(.∣.)] at *
    obtain ⟨k,hk⟩ := H
    use 4 * k - 5 * n
    calc
      n = 4 * (9 * n) + (-5) * 7 * n := by ring
      _ = 4 * (7 * k) + (-5) * 7 * n := by rw [← hk]
      _ = 7 * (4 * k - 5 * n) := by ring
  · intros H
    dsimp [(.∣.)] at *
    obtain ⟨k,hk⟩ := H
    use 9 * k
    rw [hk]
    ring

/- 4 points -/
theorem problem4c : {x : ℝ | x ^ 2 + 3 * x + 2 = 0} = {-1, -2} := by
  ext x
  dsimp
  constructor
  · intros H
    have hx :=
    calc
      (x + 1) * (x + 2) = x ^ 2 + 3 * x + 2 := by ring
      _ = 0 := by rw [H]
    rw [mul_eq_zero] at hx
    obtain hx | hx := hx
    · left; addarith [hx]
    · right; addarith [hx]
  · intros H
    obtain H | H := H
    · calc
        x ^ 2 + 3 * x + 2 = (-1) ^ 2 + 3 * (-1) + 2 := by rw [H]
        _ = 0 := by ring
    · calc
        x ^ 2 + 3 * x + 2 = (-2) ^ 2 + 3 * (-2) + 2 := by rw [H]
        _ = 0 := by ring

/- 3 points -/
theorem problem5a : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  simp
  constructor
  · intros a h
    dsimp [Int.ModEq,(.∣.)] at *
    obtain ⟨k,hk⟩ := h
    use 5 * k + 3
    calc
      a - 1 = a - 7 + 6 := by ring
      _ = 10 * k + 6 := by rw [hk]
      _ = 2 * (5 * k + 3) := by ring
  · intros a h
    dsimp [Int.ModEq,(.∣.)] at *
    obtain ⟨k,hk⟩ := h
    use 2 * k + 1
    calc
      a - 2 = a - 7 + 5 := by ring
      _ = 10 * k + 5 := by rw [hk]
      _ = 5 * (2 * k + 1) := by ring

/- 3 points -/
theorem problem5b : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp
  intros n h
  obtain ⟨h1,h2⟩ := h
  dsimp [(.∣.)] at *
  obtain ⟨k1,h1⟩ := h1
  obtain ⟨k2,h2⟩ := h2
  use -3 * k1 + 5 * k2
  calc
    n = 5 * 5 * n + (-3) * 8 * n := by ring
    _ = 5 * 5 * (8 * k2) + (-3) * 8 * n := by rw [h2]
    _ = 5 * 5 * (8 * k2) + (-3) * 8 * (5 * k1) := by rw [h1]
    _ = 40 * (-3 * k1 + 5 * k2) := by ring

theorem propContra (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  by_cases hp : P
  · constructor
    · intros hnpnq q
      apply hp
    · intros hpq np
      contradiction
  · constructor
    · intros hnpnq q
      have nq : ¬Q := hnpnq hp
      contradiction
    · intros hqp np
      by_cases hq : Q
      · have p : P := hqp hq
        contradiction
      · apply hq

/- 4 points -/
theorem problem5c :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  dsimp
  intros n
  rw [← propContra]
  simp
  intros H
  push_neg
  constructor
  · intros con
    obtain ⟨k,hk⟩ := con
    rw [hk] at H
    have kParity := Int.even_or_odd k
    obtain kEven | kOdd := kParity
    · dsimp [Int.Even] at kEven
      obtain ⟨m,kEven⟩ := kEven
      dsimp [Int.ModEq,(.∣.)] at H
      obtain ⟨c,hc⟩ := H
      rw [kEven] at hc
      have hc' : 6 * (6 * m ^ 2 - c) = 1 :=
        calc
          6 * (6 * m ^ 2 - c) = (3 * (2 * m)) ^ 2 - 6 * c := by ring
          _ = (3 * (2 * m)) ^ 2 - ((3 * (2 * m)) ^ 2 - 1) := by rw [hc]
          _ = 1 := by ring
      have contradict : 1 ≡ 0 [ZMOD 6] := by
        rw [← hc']
        dsimp [Int.ModEq]; simp
      dsimp [Int.ModEq] at contradict
      contradiction
    · dsimp [Int.Odd] at kOdd
      obtain ⟨m,kOdd⟩ := kOdd
      dsimp [Int.ModEq,(.∣.)] at H
      obtain ⟨c,hc⟩ := H
      rw [kOdd] at hc
      have hc' : 6 * (6 * m ^ 2 + 6 * m + 2 - c) = 4 :=
        calc
          6 * (6 * m ^ 2 + 6 * m + 2 - c) = ((3 * (2 * m + 1)) ^ 2 - 1) + 4 - 6 * c := by ring
          _ = 6 * c + 4 - 6 * c := by rw [← hc]
          _ = 4 := by ring
      have contradict : 4 ≡ 0 [ZMOD 6] := by
        rw [← hc']
        dsimp [Int.ModEq]; simp
      dsimp [Int.ModEq] at contradict
      contradiction
  · intros con
    obtain ⟨k,hk⟩ := con
    dsimp [Int.ModEq] at H
    mod_cases hk' : k % 3
    · dsimp [Int.ModEq,(.∣.)] at hk'
      obtain ⟨c,hc⟩ := hk'
      simp at hc
      rw [hk,hc] at H
      have obv : (2 * (3 * c)) ^ 2 - 1 = 6 * (6 * c ^ 2) - 1 := by ring
      rw [obv] at H
      dsimp [(.∣.)] at H
      obtain ⟨k',hk'⟩ := H
      have :=
        calc
          6 * (6 * c ^ 2 - k') = (6 * (6 * c ^ 2) - 1) - 6 * k' + 1 := by ring
          _ = 6 * k' - 6 * k' + 1 := by rw [hk']
          _ = 1 := by ring
      have contradict : 1 ≡ 0 [ZMOD 6] := by
        rw [← this]
        dsimp [Int.ModEq]; simp
      dsimp [Int.ModEq] at contradict
      contradiction
    · dsimp [Int.ModEq,(.∣.)] at hk'
      obtain ⟨c,hc⟩ := hk'
      have hc : k = 3 * c + 1 := by addarith [hc]
      rw [hk,hc] at H
      dsimp [(.∣.)] at H
      obtain ⟨k',hk'⟩ := H
      have hk'' : (2 * (3 * c + 1)) ^ 2 - 1 = 6 * (6 * c ^ 2 + 4 * c + 1) - 3 := by ring
      rw [hk''] at hk'
      have hk''' : 6 * (6 * c ^ 2 + 4 * c + 1 - k') = 3 := by
        calc
           6 * (6 * c ^ 2 + 4 * c + 1 - k') = 36 * c ^ 2 + 24 * c + 6 - 6 * k' := by ring
           _ = 36 * c ^ 2 + 24 * c + 6 - (6 * (6 * c ^ 2 + 4 * c + 1) - 3) := by rw [hk']
           _ = 3 := by ring
      have contradict : 3 ≡ 0 [ZMOD 6] := by
        rw [← hk''']
        dsimp [Int.ModEq]; simp
      dsimp [Int.ModEq] at contradict
      contradiction
    · dsimp [Int.ModEq,(.∣.)] at hk'
      obtain ⟨c,hc⟩ := hk'
      have hc : k = 3 * c + 2 := by addarith [hc]
      rw [hk,hc] at H
      dsimp [(.∣.)] at H
      obtain ⟨k',hk'⟩ := H
      have hk'' : (2 * (3 * c + 2)) ^ 2 - 1 = 6 * (6 * c ^ 2 + 8 * c + 3) - 3 := by ring
      rw [hk''] at hk'
      have hk''' : 6 * (6 * c ^ 2 + 8 * c + 3 - k') = 3 := by
        calc
          6 * (6 * c ^ 2 + 8 * c + 3 - k') = 36 * c ^ 2 + 48 * c + 18 - 6 * k' := by ring
          _ = 36 * c ^ 2 + 48 * c + 18 - (6 * (6 * c ^ 2 + 8 * c + 3) - 3) := by rw [hk']
          _ = 3 := by ring
      have contradict : 3 ≡ 0 [ZMOD 6] := by
        rw [← hk''']
        dsimp [Int.ModEq]; simp
      dsimp [Int.ModEq] at contradict
      contradiction

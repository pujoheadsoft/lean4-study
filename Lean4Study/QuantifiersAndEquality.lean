/- Calculational Proofs (計算的証明) -/
section CalculationalProofs

variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

example : a = e :=
  calc
    a = b     := h1
    _ = c + 1 := h2
    _ = d + 1 := congrArg Nat.succ h3
    _ = 1 + d := Nat.add_comm d 1
    _ = e     := Eq.symm h4

-- rwタクティクを使った例
example : a = e :=
  calc
    a = b     := by rw [h1]
    _ = c + 1 := by rw [h2]
    _ = d + 1 := by rw [h3]
    _ = 1 + d := by rw [Nat.add_comm d 1]
    _ = e     := by rw [h4]

-- 段階的な書き換えを一度に実行した場合
example : a = e :=
  calc
    a = d + 1 := by rw [h1, h2, h3]
    _ = 1 + d := by rw [Nat.add_comm d 1]
    _ = e     := by rw [h4]

-- simpタクティクを使った例
-- simpはいい感じにやってくれる
example : a = e := by
  simp [h1, h2, h3, h4, Nat.add_comm]

-- こんなこともできる
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

end CalculationalProofs

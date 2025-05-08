def BadMonad1 : Monad (fun α => α × Nat) where
  pure x := (x, 0)
  bind m f := let (a, n) := m; f a |> fun (b, m) => (b, n + m + 1) -- 余分な+1

-- エラーになる
-- #eval (pure 5 : Nat × Nat) >>= (fun x => (x+1, 3)) -- (6, 4) だが f a = (6,3)

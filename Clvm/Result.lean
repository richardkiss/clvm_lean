
inductive Result (α: Type n) (β:Type n) : Type (n+1)
| ok : α -> Result α β
| err : β -> String -> Result α β
deriving Repr


def is_ok (r: Result β γ) := ∃ r0, r = Result.ok r0


theorem is_ok_result_ok : is_ok ((Result.ok r) : Result α β) := by exists r


theorem not_ok : ¬ is_ok (r: Result α β) → ∃ r0, ∃ s0, r = Result.err r0 s0 := by
  induction r with
  | ok _ => simp [is_ok_result_ok]
  | err a b => intro ; exists a; exists b

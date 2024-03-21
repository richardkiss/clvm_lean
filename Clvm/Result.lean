
inductive Result (α: Type n) (β:Type n) : Type (n+1)
| ok : α -> Result α β
| err : β -> String -> Result α β
deriving Repr


def Result.is_ok {α: Type n} {β:Type n} (r: Result α β) : Bool :=
  match r with
  | Result.ok _ => True
  | Result.err _ _ => False


inductive Result (α:Type n) : Type (n+1)
| ok : α -> Result α
| err : α -> String -> Result α
deriving Repr

import tactic.linarith
import tactic.induction

example: forall (a b: nat), a + b = b + a := by intros;linarith

def split {α: Type} : list α -> list α × list α
| [] := ([] , [])
| [a] := ([a], [])
| f := (list.take (f.length/2) f,list.drop (f.length/2) f)


def merge {α : Type} (lt: α → α → bool) : list α → list α → list α
| [] a := a
| a [] := a
| (h1::t1) (h2::t2) :=
if lt h1 h2 then (h1 :: (merge t1 (h2::t2)))
else (h2 :: (merge (h1::t1) t2))


-- length is odd!

 -- if list is empty -> []
 -- if list has [a] -> [a]
 -- otherwise split

lemma smallersplit {α: Type} : ∀ (a b: α) (xs as bs: list α) , split (a::b::xs) = (as,bs) →
(as.length < (a::b::xs).length)
:=
begin
intros a b xs as bs h,
rw split at h,
cases' h,
-- match xs
-- | [] := trivial?
-- | ..
end

def mergeSort {α: Type} (f: α -> α -> bool) : list α → list α
| [] := []
| [a] := [a]
| (a::b::xs) := let p := split (a::b::xs) in
let as := p.fst in
let bs := p.snd in
let pa : as.length < (a::b::xs).length := smallersplit a b xs as bs (by tauto) in
let da : bs.length < (a::b::xs).length := sorry in
merge f (mergeSort as) (mergeSort bs)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩] }


/-
def mergeSort' : ∀ {α} , (α-> α -> bool) -> list α -> list α
:= λ α f xs , sorry
-/

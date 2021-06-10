import tactic.linarith
import tactic.induction

example: forall (a b: nat), a + b = b + a := by intros;linarith

constant x: list α 
#check list.length x 


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

lemma list.sizeof_length {α : Type} : ∀ (xs: list α) , (xs.sizeof = xs.length + 1) 
:=
begin 
  intros xs,
  induction xs, 
  case nil { refl,
    --rw list.sizeof, --unfolding sizeof
    --rw list.length,
  },
  case cons : x xs ih {
    rw list.sizeof ,
    rw list.length,
    
  }


end 

lemma smallersplit {α: Type} : ∀ (a b: α) (xs as bs: list α) , split (a::b::xs) = (as,bs) →  
(as.sizeof < (a::b::xs).sizeof) 
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
let pa : as.sizeof < (a::b::xs).sizeof := smallersplit (a::b::xs) as bs _ in
let da : bs.sizeof < (a::b::xs).sizeof := sorry in 
merge f (mergeSort as) (mergeSort bs)


/-
def mergeSort' : ∀ {α} , (α-> α -> bool) -> list α -> list α 
:= λ α f xs , sorry
-/
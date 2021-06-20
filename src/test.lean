import tactic.linarith
import tactic.induction
import data.nat.basic
open nat

example: forall (a b: nat), a + b = b + a := by intros;linarith

def split {α: Type} : list α -> list α × list α
| [] := ([] , [])
| [a] := ([a], [])
| f := (list.take (f.length/2) f, list.drop (f.length/2) f)


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
(as.length < (a::b::xs).length) --∧ bs ....
:=
begin
intros a b xs as bs h,
rw split at h,
cases' h,
simp, 
exact div_lt_self' (xs.length + 1) 0,
end

--#check div_lt_self' 

--{a: ℕ} : implicit arg. 
lemma smaller_than_its_half (a : ℕ) : (a + 2) - ((a+2)/2) < a+2 
:= 
begin 
  --rw nat.sub_lt_left_iff_lt_add,
  apply nat.sub_lt_self,
  linarith,
  simp,
  /-
  induction a,
  case nat.zero {
    sorry
  },
  case nat.succ {
    sorry
  }-/
end


lemma smallersplit_right {α: Type} : ∀ (a b: α) (xs as bs: list α) , split (a::b::xs) = (as,bs) →
(bs.length < (a::b::xs).length)
:=
begin
intros a b xs as bs h,
rw split at h,
cases' h,
simp, 
ring_nf,
apply smaller_than_its_half, 
end



def mergeSort {α: Type} (f: α -> α -> bool) : list α → list α
| [] := []
| (a::[]) := [a]
| (a::b::xs) := let p := split (a::b::xs) in
let as := p.fst in
let bs := p.snd in
--let p := (as, bs) in
--let p2 := split (a::b::xs) in
--let p2 := (bs,as) in
let pa : as.length < (a::b::xs).length := smallersplit a b xs as bs (by tauto) in
let da : bs.length < (a::b::xs).length := smallersplit_right a b xs as bs (by tauto) in
merge f (mergeSort as) (mergeSort bs)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩] }


/-
def mergeSort' : ∀ {α} , (α-> α -> bool) -> list α -> list α
:= λ α f xs , sorry
-/

/-
proving correct
1. list is sorted: define what it means to be sorted
2. list must contain all elements of the input list: no element is forgotten
3. result contains only the input elements: none new added
-/

--#2 #3
lemma output_is_perm {α: Type} (f: α -> α -> bool): ∀ (unsorted: list α),
unsorted ~ mergeSort (f) unsorted
-- input: unsortedl sortedl lists, one is sorted ver. of the other
-- output: bool if all elements in unsortedl are in sortedl
:=
begin
  intros unsorted,
  induction unsorted,
  case nil {
    rw mergeSort
  },
  case cons: a xs ih {
    cases' xs,
    case nil {
      rw mergeSort,
    },
    case cons: b bs {
      rw mergeSort,
      simp,
      -- lemma split-doesn't lose elements
      -- lemma merge doesn't lose elements


    } 
  },
end





#check list.perm
#check list.perm.nil
#check nat 
#check list

--output is sorted: defining "sorted"

-- Merging two sorted lists produces a sorted list 
lemma merging_two_sorted {α : Type} (f: α -> α -> bool): ∀ (a b: list α), 
--list.sorted a → list.sorted b →  
:=
begin
  sorry
end    
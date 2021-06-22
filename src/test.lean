import tactic.linarith
import tactic.induction
import data.nat.basic
open nat

@[elab_as_eliminator]
lemma list.strong_length_induction {α} {C : list α → Sort*}
  (rec : ∀ xs : list α, (∀ ys : list α, ys.length < xs.length → C ys) → C xs) :
  ∀ xs, C xs
| xs := rec xs (λ ys len, list.strong_length_induction ys)
using_well_founded { rel_tac := λ _ _, `[ exact ⟨_, measure_wf list.length ⟩]}

example: forall (a b: nat), a + b = b + a := by intros;linarith

def split {α: Type} : list α -> list α × list α
| [] := ([] , [])
| [a] := ([a], [])
| f := (list.take (f.length/2) f, list.drop (f.length/2) f)

/-
lemma reverse_split {α: Type} : ∀ (xs a b: list α), split xs = (a,b) → a ++ b = xs
:= 
begin
  intros xs a b hxs,
  --ext1,
  induction xs,

  case nil {
    rw split at hxs,
  },
  case cons {
    sorry
  }
end
-/

lemma add_nils {α: Type} : [] ++ [] ~ @list.nil α 
:=
begin
  refl,
end   

lemma split_preserves {α : Type} : ∀ (x a b: list α) , split x = (a, b) → 
(append a b) = x   
:=
begin
  intros x a b hx,
  cases' x,
  case nil {
    cases' hx,
    refl,
  },
  case cons: c {
    cases' x,
    case nil {
      rw split at hx,
      finish,
    },
    case cons: d {
      rw split at hx,
      cases' hx, -- cases' works here by replacing ...
      exact list.take_append_drop ((c :: d :: x).length / 2) (c :: d :: x)
    }
  }

  /-
  induction x generalizing a b, --when the indc. is too rest. generalizing the goal could be a way.
  case nil {
    rw split at hx,
    -- cases' works best here because of the constructor in the equation. 
    cases' hx,
    refl,
    --apply add_nils,
    --finish,
    --finish,
  },
  case cons: y ys ih {
    -- list.take produces a sublist and it's a sub perm 
    -- list.drop produces a sublist and it's a sub perm
    -- a is a sub perm then and b too
    -- a ++ b is a perm then 
    -/

    /-
    cases' y::ys,
    case nil {
      

    },
    case cons {

    },
    -/
end 

-- Merge

def merge {α : Type} (lt: α → α → bool) : list α → list α → list α
| [] a := a
| (h1::t1) [] := h1::t1
| (h1::t1) (h2::t2) :=
if lt h1 h2 then (h1 :: (merge t1 (h2::t2)))
else (h2 :: (merge (h1::t1) t2))

--try solving it using the first one above 

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
  induction unsorted using list.strong_length_induction with xs ih,
  simp at ih,
  cases xs,
  case nil {
    rw mergeSort
  },
  case cons: a xs {
    cases xs,
    case nil {
      rw mergeSort,
    },
    case cons: b bs {
      rw mergeSort,
      simp,
      -- lemma split-doesn't lose elements
      -- lemma merge doesn't lose elements
      -- lemma splitting produces smaller lists
      sorry
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
list.sorted a → sorted b   
:=
begin
  sorry
end    
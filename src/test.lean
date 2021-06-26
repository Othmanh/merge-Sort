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


-- notes:
-- symmetry, --flips the sides of any goal, if the goal is about a symm rel
-- induction x generalizing a b, --when the indc. is too rest. generalizing the goal could be a way.
-- cases' works best in cases where there's a constructor in the equation. 

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

lemma split_preserves_enhanced_2 {α : Type} : ∀ (x: list α) , 
(split x).fst ++ (split x).snd ~ x   
:=
begin
  intros x,
  cases' x,
  case nil {
    refl,
  },
  case cons: c {
    cases' x,
    case nil {
      rw split,
      refl,
    },
    case cons: d {
      rw split,
      simp,
      --cases' hx, -- cases' works here by replacing ...
    }
  },
end

lemma split_preserves_enhanced {α : Type} : ∀ (x: list α) , 
(split x).fst ++ (split x).snd = x   
:=
begin
  intros x,
  cases' x,
  case nil {
    refl,
  },
  case cons: c {
    cases' x,
    case nil {
      rw split,
      refl,
    },
    case cons: d {
      rw split,
      simp,
      --cases' hx, -- cases' works here by replacing ...
      --exact list.take_append_drop ((c :: d :: x).length / 2) (c :: d :: x)
    }
  }
end

/-
list.take produces a sublist and it's a sub perm 
list.drop produces a sublist and it's a sub perm
a is a sub perm then and b too
a ++ b is a perm then 
-/
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

lemma merge_preserves {α: Type} (lt: α → α → bool): ∀ (as bs: list α) ,  
merge lt as bs ~ as ++ bs  
| [] bs :=
begin
  rw merge,
  simp,
  --subst hbs, --when there's an equation, it replaces everything in the goal with the eq
end
| (a::as) [] :=
begin
  rw merge,
  simp,
end
| (a::as) (b::bs) :=
begin
  --intros x hx, --watch out that you could write non-terminating functions
  -- this will give a well founded error
  --apply merge_preserves,
  --apply hx,

  rw merge,
  by_cases hab: (lt a b: Prop),
  {
    rw [if_pos hab], --simplified hx with hab
    --subst hx,
    simp,
    apply merge_preserves as (b::bs), --matching recursion with induc.
  },
  {
    rw [if_neg hab],
    transitivity, --getting rid of the b by using transitivity
    swap,
    {
      apply list.perm_append_comm,
    },
    {
      simp,
      transitivity,
      {
        apply merge_preserves,
      },
      {
        apply list.perm_append_comm,    
      }
    }
  }
end

--?
-- added to meet the goal at the verification where it asked for 
-- the goal to be of the shape below
lemma smallersplit_2 {α: Type}: ∀ (a b: α) (bs: list α),
(split(a :: b :: bs)).fst.length < (a :: b :: bs).length
:=
begin
  intros a b bs,
  rw split,
  simp,
  ring_nf,
  exact div_lt_self' (bs.length + 1) 0,
end


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

lemma smallersplit_right_2 {α: Type} : ∀ (a b: α) (xs: list α) , 
((split (a::b::xs)).snd).length < ((a::b::xs).length)
:=
begin
intros a b xs,
rw split,
simp, 
ring_nf,
apply smaller_than_its_half, 
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

--used below
lemma list.perm_nil_cons_2 {α: Type} {y: α} {xs ys: list α}: list.nil ~ xs → xs = list.nil → xs ++ y :: ys ~ y :: ys  -- ~ @list.nil α 
:=
begin
  intros hxs hxs',
  finish,
end

lemma perm_concats_2 {α : Type}:∀ (xs xs' ys ys': list α) ,
xs ~ xs' → ys ~ ys' → xs ++ ys ~ xs' ++ ys'
:=
begin
  intros xs xs' ys ys' hxs hys,
  exact list.perm.append hxs hys,
end

lemma perm_concats {α : Type}:∀ (xs xs' ys ys': list α) ,
xs ~ xs' → ys ~ ys' → xs ++ ys ~ xs' ++ ys'
:=
begin
  intros xs xs' ys ys' hxs hys,
  cases xs,
  case nil {
    simp,
    transitivity,
    {
      apply hys,
    },
    {
      symmetry,
      cases ys',
      case nil {
        simp,
        exact list.perm.symm hxs,
      },
      case cons: y ys' { --is it okay that ys' here as a name refers to the tail of ys'
        apply list.perm_nil_cons_2,
        {
          exact hxs,
        },
        {
          exact list.perm_nil.mp (list.perm.symm hxs),
        }
      }
    
    },
    --apply list.perm.nil_eq,
  },
  case cons: x xs { --here the naming case again, xs refers to the tail of xs
    exact list.perm.append hxs hys,
  }

end

--are the curly brackets here okay?
lemma list.perm_nil_cons {α: Type} {xs ys: list α}: list.nil ~ xs → xs ++ ys ~ ys  -- ~ @list.nil α 
:=
begin
  intros hxs,
  cases ys,
  case nil {
    simp,
    exact list.perm.symm hxs,
  },
  case cons: y ys {
    sorry
  }
end   


--#2 #3
lemma output_is_perm {α: Type} (f: α -> α -> bool): ∀ (unsorted: list α),
mergeSort (f) unsorted ~ unsorted
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
      transitivity,
      {
        apply merge_preserves,
      },
      {
        transitivity,
        {
          apply perm_concats,
          apply ih,
          apply smallersplit_2, --?
          apply ih,
          apply smallersplit_right_2,
        },
        {
          apply split_preserves_enhanced_2,
        }
      }
      -- split-doesn't lose elements
      -- merge doesn't lose elements
      -- splitting produces smaller lists
    }, 
  },
end


#check list.perm
#check list.perm.nil
#check nat 
#check list

--output is sorted: defining "sorted"

-- Merging two sorted lists should produce a sorted list 
lemma merging_two_sorted {α : Type} {r : α → α → Prop} (f: α -> α -> bool): ∀ (a b: list α), 
(list.sorted r a) → sorted b   
:=
begin
  sorry
end    



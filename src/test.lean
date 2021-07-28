import tactic.linarith
import tactic.induction
import data.nat.basic
import data.list.sort
open nat

/- This lemma applies the strong induction principle on the lenght of a list. -/
@[elab_as_eliminator]
lemma list.strong_length_induction {α} {C : list α → Sort*}
  (rec : ∀ xs : list α, (∀ ys : list α, ys.length < xs.length → C ys) → C xs) :
  ∀ xs, C xs
| xs := rec xs (λ ys len, list.strong_length_induction ys)
using_well_founded { rel_tac := λ _ _, `[ exact ⟨_, measure_wf list.length ⟩]}


/- The function split takes a list α, splits it and returns the two halves in a tuple. -/
def split {α : Type} : list α → list α × list α
| xs := (list.take (xs.length/2) xs, list.drop (xs.length/2) xs)

/- This lemma proves that the first split half of a list, using the function split, is smaller in length than the original list. -/
lemma split_dec_fst {α : Type} : ∀ (x x' : α) (xs : list α),
  (split (x :: x' :: xs)).fst.length < (x :: x' :: xs).length
:=
begin
  intros x x' xs,
  simp [split],
  ring_nf,
  exact div_lt_self' (xs.length + 1) 0,
end

lemma split_dec_snd {α : Type} : ∀ (x x' : α) (xs : list α), 
  ((split (x :: x' :: xs)).snd).length < ((x :: x' :: xs).length)
:=
begin
  intros x x' xs,
  rw split,
  simp, 
  ring_nf,
  apply nat.sub_lt_self,
  linarith,
  norm_num, 
end

/- This lemma proves that concatenating the two split halves of a list produces 
   a permutation of the original list. -/
lemma split_preserves {α : Type} : ∀ (xs : list α), 
  (split xs).fst ++ (split xs).snd ~ xs   
:=
begin
  intros xs,
  simp [split]
end


/- The merge function takes two lists and recursively merges them into one ordered list. -/
def merge {α : Type} (lt : α → α → bool) : list α → list α → list α
| [] a              := a
| (h1::t1) []       := h1::t1
| (h1::t1) (h2::t2) :=
  if lt h1 h2
    then (h1 :: (merge t1 (h2::t2)))
    else (h2 :: (merge (h1::t1) t2))

/- This lemma proves that merging two lists together produces a list that is a permutation
   of the two input lists concatenated together. -/
lemma merge_preserves {α : Type} (lt : α → α → bool) : ∀ (as bs : list α),  
  merge lt as bs ~ as ++ bs   
| [] bs :=
begin
  rw merge,
  simp,
end
| (a :: as) [] :=
begin
  rw merge,
  simp,
end
| (a :: as) (b :: bs) :=
begin
  rw merge,
  by_cases hab: (lt a b : Prop),
  {
    rw [if_pos hab],
    simp,
    apply merge_preserves as (b :: bs), 
  },
  {
    rw [if_neg hab],
    transitivity, 
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

/- The function mergeSort -/
def mergeSort {α : Type} (lt : α -> α -> bool) : list α → list α
| []             := []
| [a]            := [a]
| (a :: b :: xs) :=
  let p  := split (a :: b :: xs) in
  let as := p.fst in
  let bs := p.snd in
  let h1 : as.length < (a :: b :: xs).length := split_dec_fst _ _ _ in
  let h2 : bs.length < (a :: b :: xs).length := split_dec_snd _ _ _ in
  merge lt (mergeSort as) (mergeSort bs)
  using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩] }


/- This lemma proves that sorting a list using mergeSort produces a permutation 
   of that list. -/
lemma mergeSort_preserves {α : Type} (lt : α -> α -> bool) : ∀ (xs : list α),
  mergeSort lt xs ~ xs
:=
begin
  intros unsorted,
  induction unsorted using list.strong_length_induction with xs ih,
  simp at ih,
  cases xs,
  case nil {
    rw mergeSort
  },
  case cons: x xs {
    cases xs,
    case nil {
      rw mergeSort,
    },
    case cons: x' xs {
      simp [mergeSort],
      transitivity,
      {
        apply merge_preserves,
      },
      {
        transitivity,
        {
          apply list.perm.append _ _,
          swap 3,
          apply ih,
          apply split_dec_fst,
          swap,
          apply ih,
          apply split_dec_snd,
        },
        {
          apply split_preserves,
        }
      }
    }, 
  },
end


/- This function transforms function lt to a decidable Prop. -/
def r {α : Type} (lt : α → α → bool) : α → α → Prop :=
  λ x y, lt x y = tt

/- This lemma proves that if we merge two lists using merge, all elements of
   the returned list belonged to either of the two original lists. -/
lemma element_of_merge {α : Type} (lt : α → α → bool): 
 ∀ (x : α) (as bs: list α), x ∈ merge lt as bs → x ∈ as ∨ x ∈ bs
| x [] as := 
begin
  intros hx,
  rw merge at hx,
  tauto,
end
| x (a :: as) [] := 
begin
  intros has,
  rw merge at has,
  tauto,
end
| x (a :: as) (b :: bs) :=
begin
  intros hab,
  rw merge at hab,
  by_cases hf : (lt a b : Prop), 
  { 
    rw [if_pos hf] at hab,  
    cases hab, 
    {
      left,
      left,
      exact hab,
    },
    {
      have h' := element_of_merge _ _ _ hab,
      clear element_of_merge,  
      cases h',
      {
        left,
        right,
        exact h',
      },
      {
        right,
        exact h',
      }
    }
  },
  {
    rw [if_neg hf] at hab,
    cases hab, 
    {
      right,
      exact or.inl hab, 
    },
    {
      have h' := element_of_merge _ _ _ hab,
      clear element_of_merge,
      cases h',
      {
        left,
        exact h',
      },
      {
        right,
        exact or.inr h',
      }
    }
  },
end

/- This lemma proves that, given two sorted lists, the list returned by merging 
   the two lists together using merge is sorted as well. -/
lemma merge_sorted {α : Type} (lt : α → α → bool) (tr : transitive (r lt))
(ng : ∀ x y, ¬ r lt y x → r lt x y) : ∀ (as bs: list α), 
  list.sorted (r lt) as →  
  list.sorted (r lt) bs → 
  list.sorted (r lt) (merge lt as bs)
| [] bs :=
  begin
    intros hn hbs,
    rw merge,
    exact hbs,
  end
| (a :: as) [] :=
  begin
    intros has hn,
    rw merge,
    exact has,
  end
| (a :: as) (b :: bs) :=
  begin
    intros has hbs,
    have haq : ∀ q, q ∈ as → r lt a q,
    {
      intros q hq,
      rw list.sorted at has,
      rw list.pairwise_cons at has,
      cases has with has_l has_r,
      apply has_l _ hq,
    },
    have hbq : ∀ q, q ∈ bs → r lt b q,
    {
      intros q hq,
      rw list.sorted at hbs,
      rw list.pairwise_cons at hbs,
      cases hbs with hbs_l hbs_r,
      apply hbs_l _ hq, 
    },
    rw merge,
    by_cases hf : (lt a b : Prop),
    {
      rw [if_pos hf], 
      simp,
      split, 
      { 
        intros d hm,
        have had := element_of_merge lt d as (b :: bs) hm,
        cases had,
        {
          rw list.sorted at has,
          rw list.pairwise_cons at has,
          cases has with has_l has_r,
          apply has_l _ had, 
        },
        {
          simp at had,
          cases had,
          {
            subst had, 
            exact hf,
          },
          {
            apply tr,
            {
              exact hf,
            },
            {
              simp at hbs,
              cases hbs with hbs_l hbs_r,
              apply hbs_l,
              exact had,
            }
          }
        }
      },
      {
        apply merge_sorted,
        { 
          rw list.sorted at has,
          cases has with _ _ hpas' hpas,
          exact hpas,
        },
        {
          exact hbs,
        }
      }
    },
    {
      rw [if_neg hf],
      simp,
      split,
      {
        intros k hk,
        have hk' := element_of_merge _ _ _ _ hk,
        cases hk',
        {
          cases hk',
          {
            subst hk',
            exact ng b k hf,
          },
          {
            have fak := haq _ hk',
            have fba := ng _ _ hf,
            apply tr fba fak,
          }
        },
        {
          apply hbq _,
          exact hk',
        }
      },
      {
        apply merge_sorted,
        { 
          exact has,
        },
        {
          rw list.sorted at hbs,
          cases hbs with _ _ hpbs' hpbs,
          exact hpbs,
        }
      }
    }, 
  end

/- This lemma proves that mergeSort returns a sorted list. -/
lemma mergeSort_sorts {α : Type} (lt : α → α → bool) (tr : transitive (r lt)) 
  (ng : ∀ x y, ¬ r lt y x → r lt x y) : ∀ (xs : list α), 
  list.sorted (r lt) (mergeSort lt xs)
:=
begin
  intros xs,
  induction xs using list.strong_length_induction with xs ih,
  simp at ih,
  cases xs,
  case nil {
    simp [mergeSort],
  },
  case cons: x xs {
    cases xs,
    case nil {
      simp [mergeSort],
    },
    case cons: x' xs {
      simp [mergeSort],
      apply merge_sorted lt; try { assumption },
      {
        apply ih,
        apply split_dec_fst,
      },
      {
        apply ih,
        apply split_dec_snd,
      }
    }
  },
end
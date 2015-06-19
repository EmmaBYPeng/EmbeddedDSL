Definition test := 
  fun (vec : nat -> Type) => fun (v : vec 2) => (fun (x : vec (1+1)) => x).

Definition append (A : Type) (xs : list A) (ys : list A) : list A := xs.

Fixpoint reverse (A : Type) (xs : list A) : list A :=  [case xs]
  match xs with
      | nil => []
      | cons x xs => []
  end.

Fixpoint prop_reverse A (xs : list A) : reverse A (reverse A xs) = xs.
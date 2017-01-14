Inductive list (A : Set) :=
  | nil : list A
  | cons : A -> list A -> list A.

Fixpoint length (A : Set) (a : list A) : nat :=
  match a with
  | nil _ => O
  | cons _ _ a' => S (length A a')
  end.

Fixpoint concat (A : Set) (a b : list A) : list A :=
  match a with
  | nil _ => b
  | cons _ x xs => cons A x (concat A xs b)
  end.

Theorem concat_assoc
  : forall (A : Set) (a b c : list A)
  , concat A (concat A a b) c = concat A a (concat A b c).
Proof.
  intros A a b c.
  induction a.
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHa.
  reflexivity.
Qed.

Theorem concat_length
  : forall (A : Set) (a b : list A)
  , length A (concat A a b) = length A a + length A b.
Proof.
  intros A a b.
  induction a.
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHa.
  reflexivity.
Qed.

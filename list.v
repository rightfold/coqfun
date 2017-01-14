Require Coq.Arith.Arith.

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

Fixpoint reverse (A : Set) (a : list A) : list A :=
  match a with
  | nil _ => nil A
  | cons _ x xs => concat A (reverse A xs) (cons A x (nil A))
  end.

Theorem concat_nil
  : forall (A : Set) (a : list A)
  , concat A a (nil A) = a.
Proof.
  intros A a.
  induction a.
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHa.
  reflexivity.
Qed.

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

Theorem reverse_concat
  : forall (A : Set) (a b : list A)
  , reverse A (concat A a b) = concat A (reverse A b) (reverse A a).
Proof.
  intros A a b.
  induction a.
  simpl.
  rewrite -> concat_nil.
  reflexivity.
  simpl.
  rewrite -> IHa.
  rewrite -> concat_assoc.
  reflexivity.
Qed.

Theorem reverse_reverse
  : forall (A : Set) (a : list A)
  , reverse A (reverse A a) = a.
Proof.
  intros A a.
  induction a.
  simpl.
  reflexivity.
  simpl.
  rewrite -> reverse_concat.
  simpl.
  rewrite -> IHa.
  reflexivity.
Qed.

Theorem reverse_length
  : forall (A : Set) (a : list A)
  , length A a = length A (reverse A a).
Proof.
  intros A a.
  induction a.
  simpl.
  reflexivity.
  simpl.
  rewrite -> concat_length.
  rewrite -> IHa.
  simpl.
  rewrite -> PeanoNat.Nat.add_1_r.
  reflexivity.
Qed.

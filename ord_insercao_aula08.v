(** Algoritmo de Ordenação por Inserção em listas *)

Require Import List Arith.
Open Scope nat_scope.

Fixpoint insere (n:nat) (l: list nat) :=
  match l with
  | nil => n :: nil (* lista unitária *)
  | h :: tl => if n <=? h then (n :: l) (* inserção de n na primeira posição *)
             else (h :: (insere n tl)) (* inserção de n na cauda da lista *)
  end.

Compute (insere 11 (10 :: 10 :: 10 :: nil)).
Compute (insere 0 (3 :: 9 :: 10 :: nil)).
Compute (insere 11 (10 :: 9 :: nil)).

Inductive ordenada: list nat -> Prop :=
| ord_nil: ordenada nil
| ord_one: forall x, ordenada (x :: nil)
| ord_all: forall x y l, x <= y -> ordenada (y :: l)  -> ordenada (x :: y :: l).

Lemma insere_preserva_ordem: forall l x, ordenada l -> ordenada (insere x l). 
Proof.
  induction l.
  - intros x H.
    simpl.
    apply ord_one.
  - Admitted.


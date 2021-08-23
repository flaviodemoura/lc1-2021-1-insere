

Require Import List Arith.
Open Scope nat_scope.

Fixpoint insere (n:nat) (l: list nat) :=
  match l with
  | nil => n :: nil (* lista unitária *)
  | h :: tl => if n <=? h then (n :: l) (* inserção de n na primeira posição *)
             else (h :: (insere n tl)) (* inserção de n na cauda da lista *)
  end.

Print nat.
Check nat_ind.
Print list.
Check list_ind.

Compute (insere 11 (10 :: 10 :: 10 :: nil)).
Compute (insere 0 (3 :: 9 :: 10 :: nil)).
Compute (insere 11 (10 :: 9 :: nil)).

Inductive ordenada: list nat -> Prop :=
| ord_nil: ordenada nil
| ord_one: forall x, ordenada (x :: nil)
| ord_all: forall x y l, x <= y -> ordenada (y :: l)  -> ordenada (x :: y :: l).

Check ordenada_ind.


Lemma insere_preserva_ordem: forall l x, ordenada l -> ordenada (insere x l). 
Proof.
  induction l.
  - intros x H.
    simpl.
    apply ord_one.
  - intros x H.
    simpl.
    destruct (x <=? a) eqn:Hle.
    + apply ord_all.
      * apply leb_complete.
        assumption.
      * assumption.
    + generalize dependent l.
      intro l.
      case l.
      * intros IH H.
        simpl.
        apply ord_all.
        ** apply leb_complete_conv in Hle.
           apply Nat.lt_le_incl.
           assumption.
        ** apply ord_one.
      * intros n l' IH H.
        simpl.
        destruct (x <=? n) eqn:Hle'.
        ** apply ord_all.
           *** apply leb_complete_conv in Hle.
               apply Nat.lt_le_incl.
               assumption.
           *** apply ord_all.
               **** apply leb_complete.
                    assumption.
               **** inversion H; subst.
                    assumption.
        ** inversion H; subst.
           apply ord_all.
           *** assumption.
           *** specialize (IH x).
               simpl in IH.
               rewrite Hle' in IH.
               apply IH.
               assumption.
Qed.

Lemma insere_preserva_ordem': forall l x, ordenada l -> ordenada (insere x l). 
Proof.
induction l.
  -intros x H.
  simpl.
  apply ord_one.
  -intros x H.
   simpl.
  destruct (x<=? a) eqn:Hleq.
  +apply ord_all.
  * apply leb_complete.
        assumption.
      * assumption.
    + generalize dependent l.
      intro l.
      case l.
      * intros IH H.
        simpl.
        apply ord_all.
        ** apply leb_complete_conv in Hleq.
           apply Nat.lt_le_incl.
           assumption.
        ** apply ord_one.
      * intros n l' IH H.
        simpl.
        destruct (x <=? n) eqn:Hleq'.
        ** apply ord_all.
           *** apply leb_complete_conv in Hleq.
               apply Nat.lt_le_incl.
               assumption.
              *** apply ord_all.
               **** apply leb_complete.
                    assumption.
               **** inversion H; subst.
                    assumption.
        ** inversion H; subst.
           apply ord_all.
           *** assumption.
           *** specialize (IH x).
               simpl in IH.
               rewrite Hleq' in IH.
               apply IH.
               assumption.
Qed.

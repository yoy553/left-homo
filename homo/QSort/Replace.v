(**
<<
>>
*)




Require Import Recdef.
Require Export homo.MyLib.
Require Import Sorting.Sorted Sorting.Permutation.
Require Import FunctionalExtensionality. (** for two-ends equivalences *)

  (** Selection Sort from vSort project

     - [vSort/src/QSortSSortR.v]
     - [vSort/src/QSort.v]

   *)

  

  (** * Replace
   *)

  Fixpoint replace (n: nat) (x: nat) (l: list nat) : list nat := 
    match l with 
     | [] => []
     | y::ys => if y =? n
                then x::ys
                else y::(replace n x ys)
    end.  
  Functional Scheme replace_ind 
    := Induction for replace Sort Prop.


  Lemma replace_keeps_len: forall l n m, 
     length (replace n m l) = length l.
  Proof. 
    induction l as [| x xs]; intros n m.
    - auto.
    - simpl.
      remember(x =? n) as r.
      destruct r.
      + simpl. auto.
      + simpl.
        apply eq_S. 
        apply IHxs.
  Qed.

  Lemma replace_id: 
    forall m x,
      replace x x m = m. 
  Proof.
    intros. 
    functional induction (replace x x m).    
    - reflexivity. 
    - destruct (beq_reflect y x).
      + now subst x. 
      + inversion e0.
    - now rewrite IHl. 
  Qed. 


  Lemma replace_subset: 
    forall m s h k, 
      In k (replace s h m) -> 
      In k (h::m).
  Proof.
    induction m as [| x xs]; intros * Rep.
    - simpl in Rep.
      contradiction Rep.
    - simpl in *.
      destruct (x =? s) eqn:XS.
      + destruct Rep as [Rep| Rep].
        now left.
        now (right; right).
      + destruct Rep as [Rep| Rep].
        now (right; left).
        apply IHxs in Rep.
        destruct Rep as [Rep| Rep].
        now left.
        now (right; right).
  Qed. 


  (** *** [replace_include_acc]

  *)

  Lemma replace_include_acc: 
    forall s x xs m,
      In s (x::xs) -> 
      replace s x (xs ++ m) = (replace s x xs) ++ m.
  Proof. 
    intros * IN. 
    apply in_inv in IN as [IN|IN].
    - subst s. 
      rewrite replace_id.
      rewrite replace_id.
      reflexivity. 
    - 
      induction xs as [| y ys]. 
      + inversion IN.
      + simpl.        
        apply in_inv in IN.
        destruct IN as [IN | IN]. 
        * subst s.
          rewrite <- beq_nat_refl. 
          now simpl.
        * remember (y =? s) as r. 
          {
            destruct r. 
            + now simpl. 
            + simpl.
              apply IHys in IN.
              rewrite IN. 
              reflexivity. 
          }
  Qed.

  Lemma Permutation_swap: forall {A: Type} (x1 x2: A) xs l,
      Permutation (x1::x2::xs) l -> Permutation (x2::x1::xs) l. 
  Proof. 
    intros * P12.
    cut (Permutation (x2 :: x1 :: xs) (x1 :: x2 :: xs)).
    intro C.
    apply (perm_trans C).
    apply P12.
    apply perm_swap.
  Qed.     

  
  Lemma Permutation_replce: forall p x xs,
      In p (x::xs) ->       
      Permutation (x::xs) (p::(replace p x xs)).
  Proof.
    intros * INp. simpl in INp.
    destruct INp as [INp|INp]. subst x; rewrite replace_id; apply Permutation_refl.
    functional induction (replace p x xs).
    - inversion INp.
    - apply beq_nat_true in e0.
      subst p.
      constructor.
    - simpl in INp.
      destruct INp as [INp|INp]. apply beq_nat_false in e0; contradiction.
      apply Permutation_swap.
      apply Permutation_sym.
      apply Permutation_swap.
      apply Permutation_sym.
      constructor.
      apply IHl.
      apply INp.
  Qed. 
  
  
  (** *** [Permutation_replace_both]

      If [p] is a member of [x::xs] and [y::ys]
      is a permutation of [x::xs], then [ys[p->y]]
      is a permutation of [xs[p->x]].       

   *)

  Lemma Permutation_replace_both: 
    forall x xs y ys p,
      In p (x::xs) -> 
      Permutation (x::xs) (y::ys) ->
      Permutation (replace p x xs) (replace p y ys).

  Proof. 
    intros * INx P.
    assert (INy: In p (y::ys))
      by (apply Permutation_in with (l:=x::xs); auto).
    assert (Px: Permutation (x::xs) (p::(replace p x xs))) by (apply Permutation_replce; auto).
    assert (Py: Permutation (y::ys) (p::(replace p y ys))) by (apply Permutation_replce; auto).           
    cut (Permutation (p::(replace p x xs)) (p::(replace p y ys))).
    intro C; eapply Permutation_cons_inv; apply C.

    apply Permutation_sym in Px.
    apply Permutation_sym in Py.    
    eapply perm_trans in P. 2:apply Px.
    apply Permutation_sym in P.    
    eapply perm_trans in P. 2:apply Py.
    apply Permutation_sym in P.    
    apply P.
  Qed.

  

  
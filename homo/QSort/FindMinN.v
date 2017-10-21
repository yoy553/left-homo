(**
<<
  This file contains exampls that uses [fold_left_right_tup] from [FoldLib]. 
(1) Gibbons, Geremy. The Third Homomorphism Theorem. Journal of Functional 
    Programming 6(4): 657--665, 1996.

>>
*)


Require Import Recdef.
Require Export homo.MyLib.
Require Import Sorting.Sorted Sorting.Permutation.


  (** Selection Sort from vSort project

     - [vSort/src/QSortSSortR.v]
     - [vSort/src/QSort.v]

   *)


  

  (** * Finding Smallest Value 

[findSmallest]

     The function finds the smallest [nat] among [n] and [l]. 
   *)
  
  (** ** Original functions 

   *)
  

  (** *** [findSmallest]

     The function finds the smallest [nat] among [n] 
     and [l]. 
   *)
  Fixpoint findmin (n:nat) (l: list nat) : nat :=
    match l with 
     | [] => n
     | x::xs => if x <? n 
                then findmin x xs
                else findmin n xs
    end.

  Functional Scheme findmin_ind := Induction for findmin Sort Prop.

  (** *** [findmin_r]

    Non tail-recursive version of [findmin]
   *)


  Fixpoint findmin_r (n:nat) (l: list nat) : nat :=
    match l with 
     | [] => n
     | x::xs => let y := findmin_r n xs
                in if Nat.ltb y x 
                then y
                else x
    end.
  
  Functional Scheme findmin_r_ind := Induction for findmin_r Sort Prop.

  
  (** ** Properties

   *)

  (** *** [findmin__in]

      If [s] is the smallest value in [n::l] obtained
      with [findmin], then [s] must be in [n::l]. 
   *)

  Lemma findmin__in: 
    forall l n s, 
      s = findmin n l -> In s (n::l). 
   
  (** 
----
External lemmas: 


----
Inforaml proof: 


   *)

  Proof. 
    intros l n.
    functional induction (findmin n l); intros s FS.
    - subst. now constructor. 
    - apply IHn0 in FS.
      apply in_inv in FS.
      destruct FS. 
      + subst x.
        simpl.
        right; left; reflexivity.
      + simpl.
        right; right; apply H.
    - simpl.
      simpl in IHn0.
      apply IHn0 in FS.
      intuition.
  Qed. 


  (** *** [findmin__le]

      If [s] is the smellst value in [p::m] found
      by [findmin], then [s <= p]. 
  *)

  Lemma findmin__le: 
    forall m p s, 
       s = findmin p m -> 
       s <= p.
  Proof. 
    induction m as [| x xs]; intros * FS.
    - simpl in FS.
      now subst. 
    - simpl in FS.
      remember (Nat.ltb x p) as r. 
      destruct r. 
      + symmetry in Heqr.
        apply Nat.ltb_lt in Heqr.
        apply IHxs in FS.
        omega.
      + apply IHxs; auto.
  Qed.


  (** *** [ltb_not_refl]
    
     [ltb] is not reflexivity. 
  *)

  Lemma ltb_not_refl: 
    forall x, Nat.ltb x x = false. 
  Proof. 
    induction x; auto.
  Qed. 



  (*
  Lemma partition_findmin_ge: 
    forall l p m_lt m_ge, 
      (x::xs, m_ge) = partition l p ->
      findmin x xs m_ge  = findmin x []
                                             *)

  (*
  Fixpoint findmin (n:nat) (l: list nat) : nat :=
    match l with 
     | [] => n
     | x::xs => if ltb x n 
                then findmin x xs
                else findmin n xs
    end.
  *)


  (** *** [ltb_false__not_lt]

    A conversion of false result of [ltb] 
    to the negation of [<]. 
  *)

  Lemma ltb_false__not_lt: 
    forall y x, 
      Nat.ltb x y = false -> 
      ~(x < y). 
  Proof. 
    intros * H.
    intro contr.
    apply Nat.ltb_lt in contr. 
    rewrite contr in H.
    inversion H.
  Qed. 


  (** *** [ltb_false__ge] 

    Mutual conversion between the false
    result of [ltb] and greater-than-or-equal. 
  *)

  Lemma ltb_false__ge: 
    forall y x, 
      Nat.ltb x y = false <-> 
      x >= y. 
  Proof. 
    intros. 
    apply Nat.ltb_ge. 

  (*
    split.
    - intro H.
      apply ltb_false__not_lt in H.
      omega. 
    - revert x. 
      induction y; intros x Le. 
      + unfold Nat.ltb.
        unfold leb.
        reflexivity.
      + destruct x.
        * inversion Le.
        * unfold Nat.ltb; simpl.
          unfold Nat.ltb in IHy; simpl in IHy.
          apply IHy.
          omega. 
   *)
      Qed.

    (** *** [findmin_spec]

      This is the specification of [findmin]. 
      The returned value of [findmin] is the 
      smallest value in the input list. 
    *)

  Lemma findmin_spec: 
    forall x xs s,
      s = findmin x xs -> 
      forall k, 
        In k (x::xs) ->
        s <= k. 

   (** 
----
External lemmas:


----
Informal proof: 



    *)

  Proof. 
    intros * FS * IN. 
    case IN. 
    - intro; subst x.
      apply findmin__le with (m:=xs); auto. 
    - clear IN; intro IN. 
      revert IN.
      revert k FS. 
      revert s. 
      functional induction (findmin x xs);
        intros * FS * IN. 
      + inversion IN. 
      + case IN; intro. 
        * subst k. 
          apply findmin__le with (m:=xs); auto. 
        * apply IHn; auto.
      + apply ltb_false__ge in e0.
        assert (x = n \/ x > n) as [A1 | A1] by omega; clear e0.
        * subst x.
          {
            case IN; intro. 
            - subst n.
              apply findmin__le with (m:=xs); auto. 
            - apply IHn; auto. 
          } 
        *  
          {
            case IN; intro. 
            - subst k.
              assert (A2: s <= n)
                by (apply findmin__le with (m:=xs); auto).
              cut (s < x). intro; auto with arith.
              apply le_lt_trans with (m:=n); auto.
            - apply IHn; auto. 
          } 
  Qed. 



  (** *** [permutations_share_unique_smallest_value]

    This lemma is used by [ssort_eq_perm_input] only.
    However, it is essential in bridging list data
    structure and total-ordered multiset. 
   *)

  Lemma permutations_share_unique_smallest_value: 
    forall x xs y ys, 
      Permutation (x :: xs) (y :: ys) -> 
      (findmin x xs) = (findmin y ys).

   (**
----
External lemmas: 
      - [findmin__in]
      - [findmin_spec]
      - [Permutation_sym]
      - [Permutation_in]


----
Informal proof: 

      Lets call the left-hand-side of the equation in the 
      conclusion [s_x] and the right-hand-side [s_y]. 
      Since they are the result of [findmin], 
      [In s_x (x::xs)] and [In s_y (y::ys)] by 
      [findmin__in]. Also by [findmin_spec], 
      [s_x] and [s_y] are the smallest values in 
      [x::xs] and [y::ys] respectively. However, 
      by [Permutation_in] and [Permutation_sym], 
      [s_x] is also in [y::ys] and [s_y] is also 
      in [x::xs]. Since [s_x] is the smallest in 
      [x::xs], it must be the case that [s_x <= s_y]
      and similarly [s_y <= s_x]. Therefore 
      [s_x = s_y]

   []
----
    *)

  Proof.
    intros * Perm.
    name_term s_x (findmin x xs) Sx.
    name_term s_y (findmin y ys) Sy.
    rewrite <- Sx; rewrite <- Sy.
    assert (A1: In s_x (x::xs)) 
           by (apply findmin__in with (l:=xs); auto).
    assert (A2: In s_y (y::ys)) 
           by (apply findmin__in with (l:=ys); auto).
    assert (A3: forall k, In k (x::xs) -> s_x <= k)
           by (apply findmin_spec; auto). 
    assert (A4: forall k, In k (y::ys) -> s_y <= k)
           by (apply findmin_spec; auto). 
    assert (A5: In s_x (y::ys))
      by (apply Permutation_in with (l:=(x::xs)); auto). 
    assert (A6: In s_y (x::xs))
      by (apply Permutation_sym in Perm; 
          apply Permutation_in with (l:=(y::ys)); auto). 
    assert (A7: s_y <= s_x). 
    {
      apply A4 in A5. 
      apply A5. 
    }
    assert (A8: s_x <= s_y).
    {
      apply A3 in A6. 
      apply A6. 
    }
    omega. 
  Qed. 



  (** *** [findmin_include_acc]

      I can let [findmin] preprocess the former part of the list 
      and use the result as the initial accumulator. 
   *)
  Lemma findmin_include_acc: 
    forall xs x m,
    findmin x (xs ++ m) = findmin (findmin x xs) m. 
  Proof.
    induction xs as [| y ys]; intros x m.
    - now simpl.
    - simpl.
      remember (Nat.ltb y x) as r_yx.
      destruct r_yx.
      apply IHys.
      apply IHys.
  Qed.

  Search (_ <? _ = false <-> _).
  
  Ltac ltb__lt_tac := 
    repeat match goal with
             | [H: Nat.ltb _ _ = true |- _] => 
               apply Nat.ltb_lt in H
             | [H: Nat.ltb _ _ = false |- _] => 
               apply Nat.ltb_ge in H
           end.
  

  Lemma findmin_slideout: 
    forall ys x y,
      findmin x (y::ys) = min x (findmin y ys).
  Proof. 
    intro. 
    induction ys as [| z zs]; intros.
    - simpl.
      destruct (Nat.ltb y x) eqn:Lt.
      + apply Nat.ltb_lt in Lt.
        rewrite min_r; auto with arith.
      + symmetry in Lt. symmetry in Lt.
         apply Nat.ltb_ge in Lt.
        rewrite min_l; auto with arith.
    - simpl.
      name_term x1 (findmin x zs) Xzs; rewrite <- Xzs.
      name_term y1 (findmin y zs) Yzs; rewrite <- Yzs.
      name_term z1 (findmin z zs) Zzs; rewrite <- Zzs.
      simpl in IHzs.
      destruct (Nat.ltb y x) eqn:LtXY;
      destruct (Nat.ltb z y) eqn:LtZY;
      destruct (Nat.ltb z x) eqn:LtZX.
      + subst z1.
        rewrite <- IHzs.
        rewrite LtZX.
        reflexivity.
      + ltb__lt_tac.        
        omega.
      + ltb__lt_tac.        
        rewrite min_r; auto with arith.
        apply findmin__le in Yzs.
        apply findmin__le in Xzs.
        omega.
      + ltb__lt_tac.        
        rewrite min_r; auto with arith.
        apply findmin__le in Yzs.
        apply findmin__le in Xzs.
        omega.
      + ltb__lt_tac.        
        rewrite min_r; auto with arith.
        apply findmin__le in Xzs.
        apply findmin__le in Zzs.
        omega.
      +
        subst z1.
        rewrite <- IHzs.
        rewrite LtZX.
        apply Xzs.
      + ltb__lt_tac.        
        omega.
      + subst y1.
        rewrite <- IHzs.
        rewrite LtXY.
        apply Xzs.
  Qed.        


      


  Lemma findmin_cons: 
    forall m s,
    (forall k, In k m -> s < k) ->
    s = findmin s m. 
  Proof. 
    intros m. 
    induction m as [| x xs]; intros s Lt.
    - auto.
    - simpl.
      destruct (Nat.ltb x s) eqn:xS.
      apply Nat.ltb_lt in xS.
      assert (A1: In x (x::xs)) by now left.
      apply Lt in A1. 
      omega.
      apply IHxs.
      intros. 
      apply Lt.
      now right.
  Qed. 
    

  (** ** Fold versions  

    *)

  (** *** [cr] --- [cl]

   *)


  Definition cr_fs (x n:nat) := if Nat.ltb x n then x else n.
  Definition cl_fs (n x:nat) := if Nat.ltb x n then x else n.
  Notation "x +3 y" := (cr_fs x y) (at level 60, right associativity).
  Notation "x *3 y" := (cl_fs x y) (at level 60, right associativity).


 (** *** [replace_foldr] --- [replace_foldl]

     *)

  (**
<<
  Eval compute in (findmin_foldl 3 [5,3,4]).
>>
  *)



  (** *** equivalence

   *)



  Theorem second_duality_thm_3:
    forall x y z,
      x +3 (y *3 z) = (x +3 y) *3 z.
  Proof. 
    intros; unfold cr_fs; unfold cl_fs.
    remember (Nat.ltb z y) as r_zy.
    destruct r_zy. 
    - remember (Nat.ltb x y) as r_xy.
      destruct r_xy.
      + remember (Nat.ltb x z) as r_xz. 
        destruct r_xz.
        * symmetry in Heqr_xz; apply Nat.ltb_lt in Heqr_xz. 
          assert (A1: x <= z) by omega. 
          apply ltb_false__ge in A1.
          now rewrite A1. 
        * 
          symmetry in Heqr_xz. 

          apply ltb_false__ge in Heqr_xz.
          assert (x = z \/ x > z) as [A1| A1] by omega. 
          {
            subst z.
            now rewrite ltb_not_refl.             
          }
          {
             assert (A2: Nat.ltb z x = true).
             apply Nat.ltb_lt; auto.
             now rewrite A2.
          }
      + rewrite <- Heqr_zy.
        symmetry in Heqr_zy. 
        apply Nat.ltb_lt in Heqr_zy. 
        symmetry in Heqr_xy. 
        apply ltb_false__ge in Heqr_xy.
        assert (x > z) by omega. 
        assert (A1: Nat.ltb x z = false). 
        {
          apply ltb_false__ge; auto. 
          omega. 
        }
        now rewrite A1. 
    - 
      symmetry in Heqr_zy. 
      apply ltb_false__ge in Heqr_zy. 
      remember (Nat.ltb x y) as r_xy.
      destruct r_xy. 
      + 
        symmetry in Heqr_xy. 
        apply Nat.ltb_lt in Heqr_xy. 
        assert (A1: z > x) by omega. 
        assert (A2: z >= x) by omega. 
        apply ltb_false__ge in A2. 
        now rewrite A2. 
      + 
        apply ltb_false__ge in Heqr_zy. 
        now rewrite Heqr_zy. 
  Qed.         
        
  Definition e3:= 0. 
        
  Theorem second_duality_thm_3_e:
    forall x,
      x +3 e3 = e3 +3 x. 
  Proof. 
    unfold cr_fs; unfold cl_fs. 
    intro x. 
    assert (x < e3 \/ x = e3 \/ x > e3) 
      as [A1| [A1| A1]] by omega. 
    - dupH A1 A2.
      apply Nat.ltb_lt in A1.
      rewrite A1. 
      assert (A3: x <= e3) by omega. 
      apply ltb_false__ge in A3. 
      now rewrite A3. 
    - subst x. 
      reflexivity. 
    - dupH A1 A2.
      apply Nat.ltb_lt in A1.
      rewrite A1. 
      assert (A3: x >= e3) by omega. 
      apply ltb_false__ge in A3. 
      now rewrite A3. 
  Qed. 




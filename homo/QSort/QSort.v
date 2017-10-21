(**
<<
  This file contains parition function of quicksort as an exampl 
  that tries to use [fold_left_right_tup] from [FoldLib]. 


  [1] Bird, Richard. Introduction to Functional Programming using 
                 Haskell (2nd ed.). Prentice Hall. Harlow, England.
                 1998. 
>>
*)

  Require Import Recdef.
  Require Import homo.MyLib.
  

  (** ** Partitioning 

   *)

  (** *** [partition_lt]

      We use [partition] from the List library of Coq to 
      defined [partition_lt]. 
   *)
  
  Functional Scheme partition_ind := Induction for partition Sort Prop.
  Definition f_part (p: nat) := fun x => Nat.ltb x p.

  Definition partition_lt (p: nat) (l: list nat) := partition (f_part p) l.  
  Functional Scheme partition_lt_ind := Induction for partition_lt Sort Prop.


  (** *** [partition_wont_expand]
  *)

  Lemma partition_wont_expand: 
    forall l p m_lt m_ge, 
      (m_lt, m_ge) = partition_lt p l -> 
      length m_lt <= length l /\ length m_ge <= length l.
  Proof. 
    intros l p. 
    functional induction (partition (f_part p) l); intros * P.
    - injection P; intros; subst; auto.
    - unfold partition_lt in P.
      simpl in P.
      rewrite e0 in P.
      rewrite e1 in P.
      injection P; intros; subst. 
      simpl.
      symmetry in e0.
      apply IHp0 in e0.
      intuition.
    - unfold partition_lt in P.
      simpl in P.
      rewrite e0 in P.
      rewrite e1 in P.
      injection P; intros; subst. 
      simpl.
      symmetry in e0.
      apply IHp0 in e0.
      intuition.
  Qed. 

  (** *** [partition_lt_idempotent]
   *)

  Lemma partition_lt_idempotent: 
    forall l p m_lt m_ge, 
      (m_lt, m_ge) = partition_lt p l -> 
      (m_lt, []) = partition_lt p m_lt.
  Proof. 
    intros l p.
    functional induction (partition (f_part p) l); intros * P.
    - injection P; intros; 
      now subst m_lt m_ge. 
    - unfold partition_lt in P.
      simpl in P.
      rewrite e0 in P.
      rewrite e1 in P.
      symmetry in e0.
      apply IHp0 in e0.
      injection P; intros; 
      subst m_lt m_ge. 
      simpl.
      rewrite <- e0.
      rewrite e1.
      reflexivity.
    - 
      simpl in P.
      unfold partition_lt in P.
      rewrite e0 in P.
      rewrite e1 in P.
      injection P; intros; 
      subst m_lt m_ge. 
      symmetry in e0.
      apply IHp0 in e0.
      apply e0.
  Qed. 


  (** *** [partition__lt]
   *)

  Lemma partition__lt: 
    forall l p m_lt m_ge k, 
      (m_lt, m_ge) = partition_lt p l ->
      In k m_lt -> 
      k < p.
  Proof. 
    induction l as [| y ys] ; intros * P IN. 
    - inversion P; subst.
      apply in_nil in IN; inversion IN.
    - unfold partition_lt in P.
      simpl in P.
      name_term tpl (partition (f_part p) ys) Py. 
      destruct tpl as [lo hi].
      rewrite <- Py in P.
      unfold f_part in P.
      remember (Nat.ltb y p) as r.
      destruct r. 
      + 
        injection P; intros T1 T2.
        inversion T1; clear T1.
        subst. 
        symmetry in Heqr.
        apply Nat.ltb_lt in Heqr.
        destruct IN.
        * now subst k.
        * apply IHys with (m_lt:=lo) (m_ge:=hi); auto.
      + injection P; intros; 
        subst lo.
        apply IHys with (m_lt:=m_lt) (m_ge:=hi); auto.
  Qed. 
  

  
  Lemma partition__le: 
    forall l p m_lt m_ge k, 
      (m_lt, m_ge) = partition_lt p l ->
      In k m_ge -> 
      p <= k.
  Proof. 
    induction l as [| y ys] ; intros * P IN. 
    - inversion P; subst.
      apply in_nil in IN; inversion IN.
    - unfold partition_lt in P.
      simpl in P.
      name_term tpl (partition (f_part p) ys) Py. 
      destruct tpl as [lo hi].
      rewrite <- Py in P.
      unfold f_part in P.
      remember (Nat.ltb y p) as r.
      destruct r. 
      + injection P; intros T1 T2.
        subst hi; apply IHys with (k:=k) in Py; auto.
      + symmetry in Heqr.
        apply Nat.ltb_ge in Heqr.
        injection P; intros T1 T2. 
        subst. 
        destruct IN.
        * now subst k.
        * apply IHys with (m_lt:=lo) (m_ge:=hi); auto.
  Qed. 

  Require Import Sorting.Sorted Sorting.Permutation.
  Definition join_parted (p:nat) (m_lt m_ge: list nat) :=
    m_lt ++ [p] ++ m_ge.

  Lemma partition_join_parted_permute: 
    forall m p m_lt m_ge, 
      (m_lt, m_ge) = partition_lt p m ->
      Permutation (p::m) (m_lt++[p]++m_ge). 
  Proof. 
    intros * P.
    apply Permutation_cons_app. 
    revert P.
    revert m_ge m_lt p. 
    induction m as [| x xs]; intros * P. 
    - simpl in P. 
      injection P; intros; 
      subst.
      apply perm_nil.
    - simpl in P.
      unfold partition_lt in P.
      name_term tpl (partition (f_part p) xs) Tpl.
      rewrite <- Tpl in P. 
      unfold f_part in P.
      destruct tpl as [lo hi]. 
      remember (Nat.ltb x p) as r. 
      destruct r; injection P; intros; 
        subst m_lt m_ge. 
      + apply IHxs in Tpl. 
        simpl. 
        apply perm_skip. 
        apply Tpl. 
      + apply Permutation_cons_app. 
        apply IHxs in Tpl; auto. 
  Qed. 
  
  
  Definition partition_one (l: list nat) (p: nat) :=
    (fix f (l: list nat) (z: list nat * list nat) :=
       match l with 
         | [] => z 
         | x::xs => match z with
                      | (lo, hi) => if Nat.ltb x p
                                    then f xs (lo ++ [x], hi)
                                    else f xs (lo, hi ++ [x])
                    end
       end)
      l ([],[]). 



  Lemma f_fact_7:
    forall {S1 S2 A B C D E F: Type}
           (f: S1 -> S2 -> A -> B -> C -> D -> E -> F)
           (bb:bool) s1 s2 f1 f2 f4 f5 pp1 pp2,
      f s1 s2 f1 f2
        (if bb then pp1 else pp2)
        f4 f5
      = 
      if bb then
        f s1 s2 f1 f2 pp1 f4 f5
      else
        f s1 s2 f1 f2 pp2 f4 f5        
  .
  Proof.
    intros. 
    now destruct bb.
  Qed.    

  


  
  
  (** ** Quicksort

   *)

  (** *** [qsort]
 
  *)
 
 Function qsort (m: list nat) {measure length m}:=
    match m with
      | [] => []
      | x::xs => let (m_lt, m_ge) := partition_lt x xs in
                 (qsort m_lt) ++ [x] ++ (qsort m_ge)
    end. 
  Proof. 
    -
      intros * M * P.
      symmetry in P.
      apply partition_wont_expand in P.
      simpl.
      intuition.
    - intros * M * P.
      symmetry in P.
      apply partition_wont_expand in P.
      simpl.
      intuition.
   Qed.       


  

  
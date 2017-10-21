(**
<<

                     

[1] Gibbons, Geremy. The Third Homomorphism Theorem. Journal of Functional 
    Programming 6(4): 657--665, 1996.

>>
*)


Require Import Recdef.
Require Import homo.MyLib.
Require Import homo.FoldLib.
Require Import Sorting.Sorted Sorting.Permutation.

Require Import homo.QSort.FindMinN.
Require Import homo.QSort.Replace. 
Require Import homo.QSort.QSort. 



  (** * QSort vs SSort
 
     In this section, I am going to demonstrate
     the equivalence proof between a functional version 
     of Quicksort and a variation of Selection sort
     by a generalized third homomorphism theorem 
     of Gibbons 1996 [1]. 

     The main difference from the third homomorphism 
     theorem is that the homomorphism is not of lists
     but of total-ordered multiset. Where the head value 
     of the "input" is the smallest value within the 
     "input". The approach is to view the functions 
     as the ways to reveal the total-order structure 
     of the input, which turns out to be sorting 
     operations. 

     Two pre-operations are concerned, one is [findmin]
     the other is [partition]. The former is to find
     the "head" value of the total-ordered multiset and the
     latter is to "split" the total-ordered multiset into 
     two at some location. Nonetheless to say, I am trying 
     to make correspondence between this total-order 
     multiset and list data structure with the term  
     "head" and "split", which is used by the third homomorphism
     theorem of Gibbons. 

     The important connection of this demonstration to the 
     original proof of Gibbons is that we have 
     used the essence of their proof, use of leftward 
     and rightward versions of the original functions
     and the properties of these fold functions, namely 
     the way they preprocess the two parts of the input list 
     in steps. 

   *)





  Definition join_parted (p:nat) (m_lt m_ge: list nat) :=
    m_lt ++ [p] ++ m_ge.
 

  (** ** equivalence 
   *)

  (** *** [ssort_qsort_lem]

    This corresponds to Lemma 4.3 of Gibbons 1996. 
  *)


  Definition SplitPred_le (lo hi: list nat) :=
    forall k_lo k_hi : nat,
      In k_lo lo -> In k_hi hi -> k_lo <= k_hi.

  Lemma SplitPred_le_findmin: 
    forall x xs m2, 
      SplitPred_le (x::xs) m2 -> 
      findmin x (xs ++ m2) = findmin x xs. 
  Proof. 
    intros * Sp. 
    rewrite findmin_include_acc.
    destruct m2 as [| y ys].
    - now simpl.
    - rewrite findmin_slideout.
      unfold SplitPred_le in Sp.
      name_term mx (findmin x xs) MX; rewrite <- MX.
      name_term my (findmin y ys) MY; rewrite <- MY.
      apply findmin__in in MX.
      apply findmin__in in MY.
      specialize (Sp mx my MX MY).
      apply min_l.
      auto with arith.
  Qed. 

  
  
  Lemma SplitPred_le_replace: forall s y ys m2,
      SplitPred_le (y :: ys) m2 -> 
      s = findmin y ys ->  
      replace s y (ys ++ m2) =
      (replace s y ys) ++ m2. 
  Proof.
    intros * Sp Fm. 
    assert(A1: In s (y::ys)) by (apply findmin__in; auto).
    apply replace_include_acc; auto.
  Qed. 
    



  Definition g (l: list nat) : option (nat * list nat) :=
    match l with
      | [] => None
      | x::xs => let s := findmin x xs in
                 Some (s, replace s x xs) 
    end.

 
  Lemma g_lt: 
    forall (m : list nat) (x : nat) (xs : list nat),
      g m = Some (x, xs) -> 
      lt_length xs m.
  Proof.    
    intros * G.
    unfold g in G. 
    destruct m as [| y ys] ;inversion G; clear G.
    rewrite H0 in *.
    unfold lt_length.
    rewrite replace_keeps_len. 
    auto with arith.
  Qed.
  
  Lemma SplitPred_le_ind:
   forall (m1 m2 : list nat), 
   SplitPred_le m1 m2 -> 
   forall (y : nat) (ys : list nat),
     g m1 = Some (y, ys) -> SplitPred_le ys m2.
  Proof. 
    intros * Sp * G. 
    unfold SplitPred_le.
    intros * InL InR.
    destruct m1 as [| x xs]. 
    - unfold g in G.
      inversion G.
    - simpl in G.
      inversion G.
      subst y ys.
      unfold SplitPred_le in Sp.
      apply Sp; auto.
      apply replace_subset with (s:=findmin x xs); auto.
  Qed.         




      
  Lemma g_ind__onlyif__front_update_le :
    forall (m1 m2 : list nat) (x : nat) (m1' : list nat),
      SplitPred_le m1 m2 -> 
      g m1 = Some (x, m1') ->
      g (m1 ++ m2) = Some (x, (m1' ++ m2)).
  Proof.
    intros * SP G.
    destruct m1 as [| y ys].
    - unfold g in G; inversion G. 
    - simpl in G.
      assert (x = findmin y ys /\ m1' = replace (findmin y ys) y ys) as [Gh Gt] by (inversion G; auto); clear G.
      rewrite <- app_comm_cons.
      unfold g.
      rewrite <- Gh in *.
      unfold g.
      rewrite SplitPred_le_findmin; auto. rewrite <- Gh.
      rewrite SplitPred_le_replace; auto. rewrite <- Gt.
      reflexivity.
  Qed. 
      

  
  Lemma partition_join_parted_permute: 
    forall m p m_lt m_ge, 
      (m_lt, m_ge) = partition_lt p m ->
      Permutation (p::m) (join_parted p m_lt m_ge). 
  Proof. 
    intros * P.
    unfold join_parted. 
    apply Permutation_cons_app. 
    revert P.
    revert m_ge m_lt p. 
    induction m as [| x xs]; intros * P. 
    - simpl in P. 
      injection P; intros; 
      subst.
      apply perm_nil.
    - simpl in P.
      name_term tpl (partition_lt p xs) Tpl.
      rewrite <- Tpl in P. 
      destruct tpl as [lo hi]. 
      unfold f_part in P.
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
  
  


  (** *** [ssort_r_eqv_over_permutation]

     This lemma makes a set-theoretic argument 
     about the input list: the order of the input
     list does not matter.     
   *)



  Definition list_lt_p_ge (p:nat) (m1 m2: list nat): Prop :=
    Is_true ((forallb (fun x => x <? p) m1)
               &&
               (forallb (fun x => p <=? x) m2)). 

  
  Lemma g_base__onlyif__skip_front_le: 
    forall m1 m2, 
      SplitPred_le m1 m2 -> 
      g m1 = None -> 
      m1 ++ m2 = m2.
  Proof. 
    intros. 
    destruct m1; auto.
    simpl in H0.
    inversion H0.
  Qed.     


  
  
  (** ** [ssort_seed_g]
      
   *)


  
  Function ssort_seed_g (seed m: list nat)
           {measure length m}: list nat :=
    match g m with 
     | None => seed
     | Some (x, xs) => x :: (ssort_seed_g seed xs)
    end.
  Proof. 
    intros.
    apply g_lt in teq.
    unfold lt_length in teq.
    auto.
  Defined.
  
  Lemma ssort_seed_g_inclusion_tac: 
    forall m1 m2,
      SplitPred_le m1 m2 -> 
      ssort_seed_g [] (m1 ++ m2) = 
      ssort_seed_g (ssort_seed_g [] m2) m1.
  Proof.
    Unset Ltac Debug. 
    linU_inclusion_tac
      ssort_seed_g
      ssort_seed_g_equation
      g_base__onlyif__skip_front_le
      g_ind__onlyif__front_update_le
      idtac
      SplitPred_le
      SplitPred_le_ind
    .
  Qed.






  Lemma binop_e: forall (seed: list nat), seed = []  ++ seed.
  Proof. auto. Qed.

  Lemma cr_binop_assoc: forall (a: nat) b c,
      a :: (b ++ c) = (a :: b) ++ c.
  Proof. 
    auto.
  Qed. 
  

  Lemma ssort_seed_g_slideout_tac: 
    forall m seed, 
      ssort_seed_g seed m = (ssort_seed_g [] m) ++ seed.
  Proof.
    Unset Ltac Debug. 
    linU_slideout_tac
      ssort_seed_g
      ssort_seed_g_equation
      app
      binop_e
      cr_binop_assoc
    .     
  Qed.   


  
  Lemma ssort_seed_g_homomorphism_tac_aux_inc_slide: 
    forall p m_lt m_ge , 
      SplitPred_le m_lt ([p] ++ m_ge) -> 
      SplitPred_le [p] m_ge -> 
      ssort_seed_g [] (m_lt ++ [p] ++ m_ge) = 
      (ssort_seed_g [] m_lt)
        ++ (ssort_seed_g [] [p])
        ++ (ssort_seed_g [] m_ge).
  Proof.
    intros * Sp1 Sp2.
    rewrite ssort_seed_g_inclusion_tac; auto.
    rewrite ssort_seed_g_slideout_tac. 
    rewrite ssort_seed_g_inclusion_tac; auto.
  Qed. 

  Lemma ssort_seed_g_homomorphism_tac_aux: 
    forall m_lt m_ge , 
      SplitPred_le m_lt m_ge -> 
      ssort_seed_g [] (m_lt ++ m_ge) = 
      (ssort_seed_g [] m_lt) ++ (ssort_seed_g [] m_ge).
  Proof.
    linU_homomorphism_tac
      ssort_seed_g_equation
      g_base__onlyif__skip_front_le
      g_ind__onlyif__front_update_le
      idtac
      SplitPred_le_ind
      binop_e
      cr_binop_assoc
    .     
  Qed. 

  
  
  Lemma ssort_seed_g_singleton: forall p,
    ssort_seed_g [] [p] = [p].
  Proof. 
    now repeat (rewrite ssort_seed_g_equation; simpl).
  Qed.     
  
  Lemma list_lt_p_ge__SplitPred_le: forall p m1 m2,
    list_lt_p_ge p m1 m2 -> 
    SplitPred_le m1 ([p] ++ m2)
    /\ SplitPred_le [p] m2. 
  Proof.
    intros * LE.
    split.
    - unfold SplitPred_le.
      intros * InLt InGe. 
      unfold list_lt_p_ge in LE.
      assert(A1: k_lo < p /\ p <= k_hi). 
      {
        apply Is_true_eq_true in LE.
        apply andb_true_iff in LE as [LE1 LE2].
        eapply forallb_forall in InLt.
        2:apply LE1.
        simpl in InLt.
        split. apply Nat.ltb_lt; auto.
        simpl in InGe.
        destruct InGe as [InGe | InGe].
        - rewrite InGe. auto.
        - eapply forallb_forall in InGe.
          2: apply LE2.
          simpl in InGe.
          apply Nat.leb_le; auto.
      }
      omega. 
    - unfold SplitPred_le.
      intros * InLt InGe. 
      unfold list_lt_p_ge in LE.      
      assert(A1: k_lo <= p /\ p <= k_hi). 
      {
        apply Is_true_eq_true in LE.
        apply andb_true_iff in LE as [LE1 LE2].
        simpl in InLt. destruct InLt as [InLt | InLt]. 2: inversion InLt.
        subst p.
        eapply forallb_forall in LE2.
        2:apply InGe.
        apply Nat.leb_le in LE2.        
        auto.
      }
      omega. 
  Qed.       

  
  Lemma ssort_seed_g_homomorphism_tac: 
    forall p m_lt m_ge , 
      list_lt_p_ge p m_lt m_ge -> 
      ssort_seed_g [] (m_lt ++ [p] ++ m_ge) = 
      (ssort_seed_g [] m_lt) ++ [p] ++ (ssort_seed_g [] m_ge).
  Proof.
    intros * Sp.
    apply list_lt_p_ge__SplitPred_le in Sp as [Sp1 Sp2].
    rewrite ssort_seed_g_homomorphism_tac_aux; auto.
    rewrite <- ssort_seed_g_singleton.
    rewrite ssort_seed_g_homomorphism_tac_aux; auto.    
  Qed. 

  Lemma partition_lt__list_lt_p_ge: forall m p m1 m2,
    partition_lt p m = (m1, m2) -> 
    list_lt_p_ge p m1 m2.
  Proof. 
    intro m.
    induction m as [| x xs]; intros * PL.
    - simpl in PL. inversion PL.
      subst. unfold list_lt_p_ge.
      simpl. trivial.
    - simpl in PL.
      name_term plt (partition_lt p xs) PLT.
      rewrite <- PLT in PL. destruct plt as [g d].
      unfold f_part in PL.
      symmetry in PLT.
      apply IHxs in PLT; clear IHxs.
      destruct (blt_reflect x p); inversion PL; clear PL.
      + subst m2.
        unfold list_lt_p_ge in *.
        simpl.
        apply Nat.ltb_lt in l.
        rewrite l.
        auto.
      + subst m1.
        unfold list_lt_p_ge in *.
        simpl.
        apply not_lt in n.
        apply Nat.leb_le in n.
        rewrite n; auto.
  Qed.        
    

  
  Lemma ssort_seed_g_eqv_over_permutation: 
    forall m m', 
      Permutation m m' -> 
      ssort_seed_g [] m = ssort_seed_g [] m'.

(**
----
External lemmas:
     - [permutations_share_unique_smallest_value]
     - [findmin__in]
     - [Permutation_replace_both]


----
Informal proof:

     Proof is done by mathematical induction on the 
     upper bound [k] of the input list [m], where 
     [|m| <= k]. The base case is trivial. For the inductive
     case, we destruct the list [m] into nil and cons
     [m = x::xs]. The nil case is trivial. 
     For the cons case of [m], we destruct [m']. 
     The nil case of [m'] is trivial. The cons case 
     of [m' = y::ys].

     Since [x::xs] and [y::ys] are permutation of 
     each other, their smallest values are identical. 
     So [findmin x xs = findmin y ys]. This 
     is shown by [permutations_share_unique_smallest_value]. 

     Let [p] be the smallest value in [x::xs]. With the 
     above argument, [p] is also the smallest value in [y::ys].
     By the lemma [Permutation_replace_both],
     [xs[p -> x]] and [ys[p -> y]] are also permutation of each other.

     Due to this permutation, the equality of [ssort_r [] (x::xs)] 
     and [ssort_r [] (y::ys)] is shown by the inductive 
     hypothesis where [ssort_r [] (xs[p->x])] and 
     [ssort_r [] (ys[p->y])] their respective recursive calls. 

     []     
----
   *)

  Proof.
    intro m.
    assert (exists k, length m <= k) 
      as [k K] by (exists (length m); auto).
    generalize dependent m.
    induction k as [| k]; intros m L m' Perm.
    - assert (A1: length m = 0) by omega. 
      apply length_zero_iff_nil in A1.
      subst m.
      apply Permutation_nil in Perm.
      subst m'.
      rewrite ssort_seed_g_equation.
      now simpl.
    - destruct m as [| x xs].
      + apply Permutation_nil in Perm.
        subst m'.
        rewrite ssort_seed_g_equation.
        now simpl.
      + simpl in L.
        apply le_S_n in L.
        destruct m' as [| y ys].
        * apply Permutation_sym in Perm.
          apply Permutation_nil in Perm.
          inversion Perm.
        * rewrite ssort_seed_g_equation.
          rewrite ssort_seed_g_equation.
          simpl.
          name_term p (findmin x xs) P.
          name_term p' (findmin y ys) P'.
          rewrite <- P; rewrite <- P'.
          
          dupH Perm Perm'.
          apply permutations_share_unique_smallest_value in Perm.
          rewrite Perm in P.
          rewrite <- P in P'.
          subst p'.
          
          assert (A1: In p (x::xs)). {
            rewrite <- Perm in P. 
            now apply findmin__in in P. 
          }
                                     
          assert (A2: Permutation 
                        (replace p x xs) (replace p y ys))
                by (apply Permutation_replace_both; auto).
        (* replacing with the same value, preserves permutation
         *)
        
          assert (A3: length (replace p x xs) <= k)
            by (rewrite replace_keeps_len; auto).

          apply IHk in A2; auto.
          now rewrite A2.
  Qed. 

  
  Theorem ssort_seed_g__qsort_tac: 
    forall m, 
      qsort m = ssort_seed_g [] m. 
  Proof.
    intro.
    functional induction (qsort m).
    - rewrite ssort_seed_g_equation; simpl; auto.
    - rewrite IHl, IHl0.
      rewrite <- ssort_seed_g_homomorphism_tac.
      rewrite ssort_seed_g_eqv_over_permutation with (m':=x::xs).
      reflexivity.
      apply Permutation_sym. 
      apply partition_join_parted_permute; auto.
      eapply partition_lt__list_lt_p_ge; auto.
      apply e0.
  Qed.       



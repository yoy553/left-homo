(**
<<

  Sections
    - Dual_cata: List-catamorphism
                   - A === A
                   - B === B
                   - g = g_cata
    - Rev
    - Map
    - Filter 
    - Sum
>>
*)

  Require Import homo.MyLib. 
  Require Import homo.FoldLib.
  Require Import Recdef.
  
  Section Dual_cata.
    Context { A B: Type }.
    Variable cr: A -> B -> B.
    Variable cl: B -> A -> B.
    Variable e: B.    
    
    Fixpoint cata_seed (seed: B) (m: list A) : B :=
      match m with
      | [] => seed
      | x::xs => cr x (cata_seed seed xs)
      end.
    Functional Scheme cata_seed_ind := Induction for cata_seed Sort Prop.    

    Definition SplitPred (m1 m2: list A) := True. 
    
    Lemma Base_Omitted:
      forall m1 m2,
        SplitPred m1 m2 ->
        id m1 = m1 ->
        [] ++ m2 = m2.
    Proof. 
      auto.
    Qed. 
    
    Lemma Recursive_Retention_R: 
      forall m1 m2 x m1',
        SplitPred m1 m2 -> 
        m1 = x::m1' -> 
        (m1 ++ m2) = x::(m1' ++ m2).
    Proof.
      intros; subst m1; auto.
    Qed.
    
    Lemma Recursive_Retention_L: 
      forall m1 m2,
        SplitPred m1 m2 -> 
        id m1 = m1 ->
        SplitPred m1 m2. 
    Proof.
      auto.
    Qed. 
      
    Lemma cata_seed_inclusion: 
      forall m1 m2 seed,
        SplitPred m1 m2 -> 
        cata_seed seed (m1 ++ m2) = cata_seed (cata_seed seed m2) m1.
    Proof.
     linU_inclusion_tac
       cata_seed
       cata_seed_equation
       Base_Omitted
       Recursive_Retention_R
       idatac
       SplitPred
       Recursive_Retention_L
     .
    Qed.

    Variable binop: B -> B -> B.

    (**
       Slide-Out Conditions
     *)

    Hypothesis Associative:
      forall x acc1 acc2,
        cr x (binop acc1 acc2) = binop (cr x acc1) acc2.

    Hypothesis Unit: 
      forall acc, 
        binop e acc = acc.
    
    Lemma cata_seed_slideout: forall seed m,
      cata_seed seed m = binop (cata_seed e m) seed. 
    Proof. 
    linU_slideout_tac
      cata_seed
      cata_seed_equation
      binop
      Unit
      Associative.
    Qed.    

    Lemma cata_seed_homomorophism:
      forall m1 m2,
        SplitPred m1 m2 ->         
        cata_seed e (m1++m2) = binop (cata_seed e m1) (cata_seed e m2).
    Proof.
      linU_homomorphism_tac
        cata_seed_equation
        Base_Omitted
        Recursive_Retention_R
        Head_Access
        Recursive_Retention_L
        Unit
        Associative.
    Qed. 

    Variable f: A -> B.
    Variable h: list A -> B.

    Hypothesis List_Homomorphism:
      h [] = e /\
      (forall a, h [a] = f a) /\
      forall m1 m2,
        h (m1 ++ m2) = binop (h m1) (h m2).

    Hypothesis split: list A -> (list A * list A).

    Hypothesis split_pred: forall m m1 m2,
        split m = (m1,m2) -> m = m1 ++ m2.

    Hypothesis Singleton:
      forall x, cr x e = f x.

    
    Proposition Leftward_Homomorphism:
      forall m,
        cata_seed e m = h m.
    Proof.
      intro m.
      destruct List_Homomorphism as [H1 [H2 H3]].      
      assert (exists k, length m <= k) as [k K]
          by (exists (length m); auto).
      revert m K.

      induction k as [| k]; intros * K.
      {
        assert (A1: length m = 0) by omega. 
        apply length_zero_iff_nil in A1. subst m.
        now simpl.
      }         
      destruct m as [| x xs]; simpl; auto. simpl in K. 
      assert (K': length xs <= k) by omega; clear K; rename K' into K.

      assert (A2: exists m1 m2, xs = m1 ++ m2).
      {
        exists xs. exists []. now rewrite app_nil_r.
      }
      destruct A2 as [m1 [m2 A2]].
      rewrite A2.
      rewrite A2 in K.
      dupH K K'.
      rewrite app_length in K.
      assert (A3: length m1 <= k) by omega.
      assert (A4: length m2 <= k) by omega.
      assert (A5: SplitPred m1 m2) by (unfold SplitPred; auto).
      rewrite cata_seed_homomorophism; auto.
      rewrite IHk; auto.
      rewrite IHk; auto.
      rewrite <- H3.
  Abort.      
      
          
  End Dual_cata.
    



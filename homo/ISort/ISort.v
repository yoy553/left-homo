(**
<<
  This file is to examing the equivalence between msort and isort, to 
  see if I really need 3rd homomorphsim of Gibbons 1996. 


  Gibbons, Geremy. The Third Homomorphism Theorem. Journal of Functional 
       Programming 6(4): 657--665, 1996.

>>
*)


  Require Import homo.MyLib. 
  Require Import homo.FoldLib.   
  Require Import Recdef.  

  Fixpoint ins (k: nat) (m: list nat) :=
    match m with 
      | nil => [k]
      | x::xs => if k <=? x then k::m
                 else x::(ins k xs)
    end.

  Fixpoint isort (m: list nat) :=
    match m with 
      | [] => []
      | x::xs => ins x (isort xs)
    end. 


  Fixpoint isort_tr (acc m: list nat) :=
    match m with 
      | [] => acc
      | x::xs => isort_tr (ins x acc) xs
    end. 

  Eval compute in (isort [1,4,2,3,2]).
  Eval compute in (isort_tr [] [1,4,2,3,2]).


  Fixpoint isort_seed (seed m: list nat) :=
    match m with 
      | [] => seed
      | x::xs => ins x (isort_seed seed xs)
    end. 

  Lemma isort_seed_inclusion: 
    forall m1 m2 seed, 
      isort_seed seed (m1 ++ m2) = isort_seed (isort_seed seed m2) m1.
  Proof. 
    intro m1.
    induction m1 as [| x xs]; intros. 
    - reflexivity.
    - simpl.
      cut (isort_seed seed (xs ++ m2)
           = isort_seed (isort_seed seed m2) xs).
      intro C. now rewrite C.
      apply IHxs.
  Qed. 
  Functional Scheme isort_seed_ind :=
    Induction for isort_seed Sort Prop.

  Definition SplitPred (m1 m2: list nat) := True.

  Definition g (m : list nat) := m.
  
  Lemma Base_Omitted:
    forall (m2: list nat),
      True -> True ->
      [] ++ m2 = m2.
  Proof. 
    trivial.
  Qed.     

  Definition scat (m1 m2: list nat) := m1 ++ m2.

  
  Lemma Recursive_Retension_R :
    forall (m1 m2 : list nat) (x : nat) (xs : list nat),
      True -> 
      m1 = x :: xs ->
      m1 ++ m2 = x :: (xs ++ m2).
  Proof.
    intros * SP G.
    subst m1.
    simpl.
    reflexivity.
  Qed.


    
  (**
     We forcus on merge sort, so we will use an inefficeint
     version as it is done by CPDT Sec 7.1.
<<
  Function merge (m1 m2: list nat) {measure length2 (m1, m2)} :=
    match m1, m2 with
      | [], _ => m2
      | _, [] => m1
      | (x::xs), (y::ys) => if blt_nat x y 
                            then x::(merge xs m2)
                            else y::(merge m1 ys)
    end.
>>
  *)


  Fixpoint mergeS (m1 m2: list nat) :=
    match m1 with
      | [] => m2
      | x::xs => ins x (mergeS xs m2)
    end. 



  

  Definition mergeS_r (m1 m2: list nat) := fold_right ins m2 m1.

  Lemma mergeS__mergeS_r: 
    forall m1 m2,
      mergeS m1 m2 = mergeS_r m1 m2.
  Proof. 
    induction m1; intro; simpl.
    - reflexivity.
    - rewrite <- IHm1.
      reflexivity.
  Qed.


  (**
[[
          x * (y * z) = y * (x * z)

          (z * y)
]]

   *)


  Lemma ins_comm: 
    forall z x y, 
      ins x (ins y z) = ins y (ins x z).
  Proof. 
    intros.
    induction z as [| z zs].
    - simpl.
      destruct (ble_reflect x y) as [Hxy|Hxy];
        destruct (ble_reflect y x) as [Hyx|Hyx];
        auto. 
      now destruct (Nat.le_antisymm x y Hxy Hyx).
      omega.
    - simpl.
      repeat match goal with
             | |- context[?X <=? ?Y] =>
               let Hxy := fresh "Hxy" in
               destruct (ble_reflect X Y) as [Hxy|Hxy]; auto; simpl
             end;
        try contradiction;
        try omega;
        repeat match goal with
               | Hxy : ?X <= ?Y |- _ => 
                 match goal with
                 | Hyx: Y <= X |- _ =>
                   
                   destruct (Nat.le_antisymm X Y Hxy Hyx); auto
                 end
               end.
      now rewrite IHzs.
  Qed.       

  
      
  Lemma ins_mergeS_assoc: 
    forall i m1 m2,
      ins i (mergeS m1 m2) = mergeS (ins i m1) m2.
  Proof. 
    intros i m1. 
    assert (exists k, length m1 <= k) as [k K]
      by (exists (length m1); auto).
    revert i m1 K.
    induction k as [| k]; intros * K *.
    - assert (A1: length m1 = 0) by omega. 
      apply length_zero_iff_nil in A1.
      subst m1. 
      reflexivity.
    - destruct m1 as [| y ys].
      + reflexivity.
      + simpl in K.
        apply le_S_n in K.
        simpl.
        case (i <=? y) eqn: iLEy.
        * simpl.
          rewrite IHk; auto.
        * simpl.
          rewrite <- IHk; auto.
          apply ins_comm.
  Qed. 


  Lemma isortS_seed_slideout: 
    forall m seed, 
      isort_seed seed m = mergeS (isort_seed [] m) seed.
  Proof. 
    induction m as [| x xs]; intros. 
    - now simpl.
    - simpl.
      rewrite IHxs.
      destruct xs.
      simpl. reflexivity.
      simpl.
      apply ins_mergeS_assoc.
  Qed. 



  Lemma isortS_homomorphism: 
    forall m m1 m2,  
      (m1, m2) = unapp_half m -> 
      mergeS (isort_seed [] m1) (isort_seed [] m2) = 
      isort_seed [] (m1 ++ m2). 
  Proof. 
    intros * SP. 
    name_term lhs (mergeS (isort_seed [] m1) (isort_seed [] m2)) LHS.
    rewrite <- LHS.
    rewrite isort_seed_inclusion.
    rewrite isortS_seed_slideout. 
    now subst lhs.
  Qed. 



  
  Lemma isortS_homomorphism_tac: 
    forall m1 m2,  
      SplitPred m1 m2 -> 
      isort_seed [] (scat m1 m2) = mergeS (isort_seed [] m1) (isort_seed [] m2).
  Proof. 
    Abort.
    
      
      
      
  Lemma isort__isort_seed: 
    forall m,
      isort m = isort_seed [] m.
  Proof.
    intro. induction m; simpl; auto.
    now rewrite IHm.
  Qed. 

  
  Function msortS (m: list nat) {measure length m}:=
    match m with
      | [] => []
      | [x] => [x]
      | _ => let (m1, m2) := unapp_half m in
             mergeS (msortS m1) (msortS m2)
    end. 
  Proof.
    - intros.
      unfold unapp_half in teq1.
      symmetry in teq1.
      name_term len_x_n_l0 (length (x::n::l0)) LEN.
      rewrite <- LEN in *.
      simpl in LEN.
      assert (L0: len_x_n_l0 > 0) by omega.
      apply lt_div2 in L0.
      assert (len_x_n_l0 - div2 len_x_n_l0 > 0) by (apply gt_minus; auto).
      symmetry in teq1.
      apply unapp_reduce_m2 in teq1; auto.
      simpl in teq1.
      rewrite <- LEN in *.
      apply teq1.
      simpl.
      auto with arith.
    - intros. 
      unfold unapp_half in teq1.
      apply unapp_reduce_m1 in teq1.
      apply teq1. clear teq1.
      name_term len_x_n_l0 (length (x::n::l0)) LEN.
      rewrite <- LEN in *.
      simpl in LEN.
      assert (L0: len_x_n_l0 > 0) by omega.
      apply lt_div2 in L0.
      assert (L1: len_x_n_l0 > 1) by omega.
      rewrite LEN at 2.
      simpl.
      omega. 
  Defined. 


  Theorem isort__msortS: 
    forall m, 
      isort m = msortS m.
  Proof. 
    intro m.
    rewrite isort__isort_seed. 
    assert (exists k, length m <= k) 
      as [k K] by (exists (length m); auto). 
    revert m K.
    induction k as [| k]; intros * K.
    - assert (A1: length m = 0) by omega. 
      apply length_zero_iff_nil in A1.
      now subst m.
    - destruct m as [| x1 xs]. now simpl.
      destruct xs as [| x2 xs]. now simpl.
      rewrite msortS_equation. 
      name_term tpl (unapp_half (x1::x2::xs)) Tpl;
        rewrite <- Tpl; destruct tpl as [m1 m2].
      simpl in K. 
      assert (K': S (length xs) <= k) by (rewrite le_S_n; auto); 
        clear K; rename K' into K.
      assert (length m1 <= length (x2::xs) 
              /\ length m2 <= length (x2::xs))
        as [A1 A2]. {
        symmetry in Tpl.
        apply unapp_half_nonnil_reduces in Tpl; auto.
        2: simpl; omega. 
        simpl in *.
        omega. 
      }
      simpl in A1, A2.
      assert (A3: length m1 <= k) by omega; clear A1.
      assert (A4: length m2 <= k) by omega; clear A2. 
      rewrite <- (IHk m1 A3); rewrite <- (IHk m2 A4).      
      rewrite isortS_homomorphism with (m:=(x1::x2::xs)); auto.
      apply unapp_half_app in Tpl.
      now rewrite Tpl. 
  Qed. 

      


  (** * MergeS with efficient definition 

   *)


  Definition length2 (m: (list nat) * (list nat)):= 
    match m with 
      | (m1,m2) => (length m1)+(length m2)
   end.

  Function merge (m: list nat * list nat) {measure length2 m} :=
    match m with
      | ([], m2) => m2
      | (m1, []) => m1
      | ((x::xs), (y::ys)) => if x <=? y 
                            then x::(merge (xs, y::ys))
                            else y::(merge (x::xs, ys))
    end.
  Proof. 
    - intros.
      unfold length2; simpl; omega. 
    - intros.
      unfold length2; simpl; omega. 
  Defined.
    

  (**

[[
       i * (m1 + m2) = (i*m1) + m2
]]
   *)

  Lemma ins_merge: forall m k,
      ins k m = merge ([k],m). 
  Proof. 
    intro m.
    induction m as [| x xs]; intro; rewrite merge_equation; simpl.
    - reflexivity. 
    - destruct (ble_reflect k x).
      + rewrite merge_equation. 
        reflexivity. 
      + rewrite IHxs.
        reflexivity. 
  Qed.
  
  Ltac le_leb_tac :=
    repeat
        match goal with
        | [H: ~ ?X <= ?Y |- _] =>          
          match goal with
          | [Hxy: (X <=? Y) = false |- _] => idtac
          | _ => apply Nat.leb_nle in H; try rewrite H
          end

        | [H: ?X <= ?Y |- _] =>

          match goal with
          | [Hxy: (X <=? Y) = true |- _] => idtac
          | _ => apply Nat.leb_le in H; try rewrite H
          end
        | [H: ?X > ?Y |- _] =>
          match goal with
          | [Hxy: (X <=? Y) = false |- _] => idtac
          | _ => apply Nat.leb_gt in H; try rewrite H
          end
          
        | [H: ?Y < ?X |- _] =>

          match goal with
          | [Hxy: (X <=? Y) = false |- _] => idtac
          | _ => apply Nat.leb_gt in H; try rewrite H
          end
            
        | [|- context [?X <=? ?X]] => rewrite Nat.leb_refl

        | [|- context [?X <=? ?Y]] =>
          match goal with
          | [Hxy: (X <=? Y) = _ |- _] => rewrite Hxy
          | _ => idtac
          end
        end.
  
  Ltac leb__leb_tac :=
    repeat match goal with
    | [H: (?X <=? ?Y) = _ |- context [?X <=? ?Y]] => rewrite H
    end.
  
  Ltac rm_neg_le_tac := 
    repeat match goal with
           | [H: ~ ?X <= ?Y |- _] =>
             let A := fresh "A" in assert (A: X > Y) by omega
                                   ; clear H
           end.

                
  Lemma ins_merge_assoc: 
    forall m1 m2 i,
      ins i (merge (m1, m2)) = merge ((ins i m1), m2).
  Proof. 
    intros m1 m2.
    assert (exists k, k >= length2 (m1,m2)) 
      as [k K] by (exists (length2 (m1,m2)); auto).
    revert m1 m2 K. 
    induction k; intros. 
    - apply le_n_0_eq in K.
      destruct m1; destruct m2;
      simpl in K; inversion K. 
      simpl; rewrite merge_equation; reflexivity.
    - destruct m1 as [| h1 m1]; destruct m2 as [|h2 m2].
      + simpl; rewrite merge_equation; reflexivity.
      +
        assert (K': k >= length2 ([], m2)). 
        {
          simpl in K.
          now apply le_S_n in K.
        }
        clear K; rename K' into K.
        apply IHk with (i:=i) in K.
        simpl.
        rewrite merge_equation.
        case (i <=? h2) eqn: iLEh2.
        * rewrite merge_equation.
          reflexivity.
        * simpl in K.
          rewrite <- K.
          rewrite merge_equation.
          reflexivity.
      + 
        assert (K': k >= length2 (m1,[])). 
        {
          simpl in K.
          now apply le_S_n in K.
        }
        clear K; rename K' into K.
        apply IHk with (i:=i) in K.
        simpl.
        rewrite merge_equation.
        case (i <=? h1); trivial.
      + 
        simpl.
        rewrite merge_equation.

        assert (h1 = h2 \/ h1 < h2 \/ h1 > h2) as [XY| [XY | XY]] by omega. 
        * subst h1.
          rewrite Nat.leb_refl.
          destruct (ble_reflect i h2); simpl.
          {
            - apply Nat.leb_le in l. rewrite l.
              symmetry. 
              rewrite merge_equation.
              rewrite l.
              rewrite merge_equation.
              rewrite Nat.leb_refl.
              reflexivity.
          } 
          apply Nat.leb_nle in n.
          rewrite n.
          symmetry. 
          rewrite merge_equation.
          rewrite Nat.leb_refl.
          assert ( k >= length2 (m1, h2 :: m2) ) by (simpl in *; omega).
          rewrite IHk; auto.
        *
          assert(A1: h1 <= h2) by omega. 
          Search((_ <=? _) = true <-> _ ). 
          apply Nat.leb_le in A1.
          rewrite A1.
          assert (k >= length2 (m1, h2 :: m2)) by (simpl in *; omega). 
          {
            assert (i < h1 \/ i = h1 \/ (h1 < i < h2) \/ h2 = i \/ h2 < i) as
                [ZX| [ZX | [[H1I IH2] |[YZ|YZ]]]] by omega. 
            -
              assert (A2: i <= h1) by omega.
              simpl.
              apply Nat.leb_le in A2. rewrite A2.
              symmetry.
              rewrite merge_equation.
              assert (A3: i <= h2) by omega.  
              apply Nat.leb_le in A3. rewrite A3.
              rewrite merge_equation.
              rewrite A1.
              reflexivity.
            - subst i.
              simpl.
              rewrite Nat.leb_refl. 
              symmetry.
              rewrite merge_equation.
              rewrite merge_equation.
              rewrite A1.
              reflexivity.
            - simpl.
              apply Nat.leb_gt in H1I. 
              rewrite  H1I.
              symmetry. 
              rewrite merge_equation.
              rewrite A1.
              rewrite IHk; auto.
            - subst i.
              simpl.
              apply Nat.leb_gt in XY. rewrite XY.
              symmetry.
              rewrite merge_equation. rewrite A1.
              rewrite IHk; auto.
            - assert (A2: i > h1) by omega. 
              simpl.
              apply Nat.leb_gt in A2. rewrite A2.
              symmetry.
              rewrite merge_equation.
              rewrite A1.
              rewrite IHk; auto.
          }
        *
          dupH XY H1H2.
          apply Nat.leb_gt in H1H2.
          rewrite H1H2.
          assert (A1: h2 <= h1) by omega. 
          assert (k >= length2 (h1::m1, m2)) by (simpl in *; omega). 
          {
            assert (i < h2 \/ i = h2 \/ (h2 < i < h1) \/ h1 = i \/ h1 < i) as
                [ZX| [ZX | [[H1I IH2] |[YZ|YZ]]]] by omega. 
            -
              assert (A2: i <= h2) by omega. 
              assert (A3: i <= h1) by omega. 
              simpl.
              apply Nat.leb_le in A2. 
              apply Nat.leb_le in A3.
              rewrite A2, A3.
              symmetry.
              rewrite merge_equation.
              rewrite A2.
              rewrite merge_equation.
              rewrite H1H2.
              reflexivity.
            - subst i.
              simpl.
              rewrite Nat.leb_refl.
              apply Nat.leb_le in A1; rewrite A1.
              symmetry.
              rewrite merge_equation.
              rewrite Nat.leb_refl.
              rewrite merge_equation.
              rewrite H1H2.
              reflexivity.
            - simpl.
              apply Nat.leb_gt in H1I; rewrite H1I.
              assert (A2: i <= h1) by omega. 
              apply Nat.leb_le in A2; rewrite A2.
              symmetry. 
              rewrite merge_equation.
              rewrite H1I.
              rewrite IHk; auto.
              simpl.
              rewrite A2.
              reflexivity.
            - subst i.
              simpl.
              assert (A2: h2 <= h1) by omega.
              apply Nat.leb_gt in XY.
              rewrite Nat.leb_refl.
              rewrite XY.
              symmetry.
              rewrite merge_equation.
              rewrite XY.
              rewrite IHk; auto.
              simpl.
              rewrite Nat.leb_refl.
              reflexivity.
            - 
              assert (A2: i > h2) by omega. 
              simpl.
              apply Nat.leb_gt in A2.
              apply Nat.leb_gt in YZ.
              rewrite YZ, A2.
              symmetry.
              rewrite merge_equation.
              apply Nat.leb_gt in XY. rewrite XY.
              rewrite IHk; auto.
              simpl.
              rewrite YZ.
              reflexivity.
          }

    Restart.

    intros m1 m2.
    assert (exists k, k >= length2 (m1,m2)) 
      as [k K] by (exists (length2 (m1,m2)); auto).
    revert m1 m2 K. 
    induction k; intros. 
    - apply le_n_0_eq in K.
      destruct m1; destruct m2;
      simpl in K; inversion K. 
      simpl; rewrite merge_equation; reflexivity.
    - destruct m1 as [| h1 m1]; destruct m2 as [|h2 m2].
      + simpl; rewrite merge_equation; reflexivity.
      +
        assert (K': k >= length2 ([], m2)). 
        {
          simpl in K.
          now apply le_S_n in K.
        }
        clear K; rename K' into K.
        apply IHk with (i:=i) in K.
        simpl.
        rewrite merge_equation.
        case (i <=? h2) eqn: iLEh2.
        * rewrite merge_equation.
          reflexivity.
        * simpl in K.
          rewrite <- K.
          rewrite merge_equation.
          reflexivity.
      + 
        assert (K': k >= length2 (m1,[])). 
        {
          simpl in K.
          now apply le_S_n in K.
        }
        clear K; rename K' into K.
        apply IHk with (i:=i) in K.
        simpl.
        rewrite merge_equation.
        case (i <=? h1); trivial.
      + 
        simpl.
        rewrite merge_equation.

        assert (h1 = h2 \/ h1 < h2 \/ h1 > h2) as [XY| [XY | XY]] by omega. 
        * subst h1.
          rewrite Nat.leb_refl.
          destruct (ble_reflect i h2); simpl.
          {
            apply Nat.leb_le in l. rewrite l.
            symmetry. 
            rewrite merge_equation.
            rewrite l.
            rewrite merge_equation.
            rewrite Nat.leb_refl.
            reflexivity.
          } 
          apply Nat.leb_nle in n.
          rewrite n.
          symmetry. 
          rewrite merge_equation.
          rewrite Nat.leb_refl.
          assert ( k >= length2 (m1, h2 :: m2) ) by (simpl in *; omega).
          rewrite IHk; auto.
        *
          assert(A1: h1 <= h2) by omega.
          assert (k >= length2 (m1, h2 :: m2)) by (simpl in *; omega). 
          {
            assert (i < h1 \/ i = h1 \/ (h1 < i < h2) \/ h2 = i \/ h2 < i) as
                [ZX| [ZX | [[H1I IH2] |[YZ|YZ]]]] by omega. 
            -
              assert (A2: i <= h1) by omega.
              assert (A3: i <= h2) by omega.
              le_leb_tac.
              symmetry; rewrite merge_equation.
              rewrite merge_equation.
              repeat leb__leb_tac.
              simpl.
              leb__leb_tac.
              reflexivity.
            - subst i.
              le_leb_tac.
              symmetry.
              rewrite merge_equation.
              rewrite merge_equation.
              leb__leb_tac.
              simpl.
              le_leb_tac.
              reflexivity.
            - le_leb_tac.
              symmetry; rewrite merge_equation.
              simpl.
              leb__leb_tac.
              rewrite IHk; auto.
            - subst i.
              le_leb_tac.
              symmetry; rewrite merge_equation.
              simpl.
              leb__leb_tac.
              rewrite IHk; auto.
            - assert (A2: i > h1) by omega. 
              le_leb_tac.
              symmetry; rewrite merge_equation; simpl.
              leb__leb_tac.
              rewrite IHk; auto.
          }
        *
          dupH XY H1H2.
          assert (A1: h2 <= h1) by omega. 
          le_leb_tac.
          assert (k >= length2 (h1::m1, m2)) by (simpl in *; omega). 
          {
            assert (i < h2 \/ i = h2 \/ (h2 < i < h1) \/ h1 = i \/ h1 < i) as
                [ZX| [ZX | [[H1I IH2] |[YZ|YZ]]]] by omega. 
            -
              assert (A2: i <= h2) by omega. 
              assert (A3: i <= h1) by omega. 
              simpl.
              symmetry; rewrite merge_equation.
              le_leb_tac.
              rewrite merge_equation.
              leb__leb_tac.
              reflexivity.
            - subst i.
              simpl.
              
              leb__leb_tac.
              le_leb_tac.
              rewrite Nat.leb_refl.
              le_leb_tac.              
              symmetry; rewrite merge_equation.
              le_leb_tac.
              rewrite Nat.leb_refl.
              rewrite merge_equation.
              rewrite H1H2.
              reflexivity.
            - simpl.
              apply Nat.leb_gt in H1I; rewrite H1I.
              assert (A2: i <= h1) by omega. 
              apply Nat.leb_le in A2; rewrite A2.
              symmetry. 
              rewrite merge_equation.
              rewrite H1I.
              rewrite IHk; auto.
              simpl.
              rewrite A2.
              reflexivity.
            - subst i.
              simpl.
              assert (A2: h2 <= h1) by omega.
              apply Nat.leb_gt in XY.
              rewrite Nat.leb_refl.
              rewrite XY.
              symmetry.
              rewrite merge_equation.
              rewrite XY.
              rewrite IHk; auto.
              simpl.
              rewrite Nat.leb_refl.
              reflexivity.
            - 
              assert (A2: i > h2) by omega. 
              simpl.
              apply Nat.leb_gt in A2.
              apply Nat.leb_gt in YZ.
              rewrite YZ, A2.
              symmetry.
              rewrite merge_equation.
              apply Nat.leb_gt in XY. rewrite XY.
              rewrite IHk; auto.
              simpl.
              rewrite YZ.
              reflexivity.
          }
(*
    Restart.

      intro m1. induction m1 as [| x xs]; intros;
                  destruct m2 as [| y ys]; simpl.
    - rewrite merge_equation. 
      reflexivity.
    - rewrite merge_equation.            
      destruct (ble_reflect i y); simpl. 
      + now rewrite merge_equation. 
      + now rewrite ins_merge. 
    - destruct (ble_reflect i x).
      + now rewrite merge_equation.
      + now rewrite merge_equation.
    - rewrite merge_equation.
      destruct (ble_reflect x y);
        destruct (ble_reflect i x); simpl.
      + assert (A1: i <= y) by omega. le_leb_tac.

        leb__leb_tac.
        symmetry; rewrite merge_equation.
        le_leb_tac; leb__leb_tac.
        rewrite merge_equation.         
        leb__leb_tac.
        reflexivity.
      + le_leb_tac.
        symmetry; rewrite merge_equation.
        leb__leb_tac.
        leb__leb_tac.
        now rewrite IHxs.
      + symmetry; rewrite merge_equation.
        destruct (ble_reflect i y).
        * rewrite merge_equation.
          le_leb_tac.
          reflexivity.
        * 
          {
            destruct ys as [| z zs].
            - le_leb_tac.
              rewrite merge_equation.
              rewrite merge_equation.            
              le_leb_tac.
              simpl.
              rewrite l.
              reflexivity.
            - rewrite merge_equation.
              rewrite merge_equation.
              destruct (ble_reflect i z);
                destruct (ble_reflect x z); simpl.       
              + le_leb_tac.
                leb__leb_tac.                
                reflexivity.
              + le_leb_tac.
                leb__leb_tac.                  
                reflexivity.
              + omega. 
              + le_leb_tac.
                leb__leb_tac.
                destruct zs as [| b bs]; simpl.
                * rewrite merge_equation.                
                  leb__leb_tac.
                  reflexivity. 
                * rewrite merge_equation.                
                  destruct (ble_reflect i b).
                  rewrite merge_equation.                

                  
          }
          
      +
        assert (A1: x > y) by omega. 
        assert (A2: i > x) by omega. 
        assert (A3: i > y) by omega. 
        assert (A4: ~i <= y) by omega. 
        apply Nat.leb_nle in A4; rewrite A4.
        symmetry; rewrite merge_equation.
        apply Nat.leb_nle in n; rewrite n.        


        XXX
          
        destruct [].
        
        assert (A1: y < x) by omega.
        destruct (ble_reflect i y).
        * rewrite merge_equation.
          apply Nat.leb_nle in n.
          rewrite n.
          reflexivity.
        * symmetry. rewrite merge_equation. reflexivity. 
          
          apply Nat.leb_le in l. rewrite l.
        
        reflexivity. 
        destruct ys as [| z zs].
        * rewrite merge_equation. reflexivity. 
        * rewrite merge_equation.
          destruct (ble_reflect i z); simpl.
          apply Nat.leb_le in l. rewrite l. rewrite merge_equation. reflexivity. 
          apply Nat.leb_nle in n0. rewrite n0. 
          rewrite merge_equation. reflexivity.
                          Search (_ <=? _ = false  <-> _).


                          rewrite merge_equation. reflexivity.
                          rewrite merge_equation. reflexivity.
          rewrite merge_equation. reflexivity. 
          
        intros m1 m2.  
    functional induction (merge (m1,m2)); intro. 

*)    
  Qed. 

  

  Lemma isort_seed_slideout: 
    forall m seed, 
      isort_seed seed m
      = merge ((isort_seed [] m), seed).
  Proof. 
    induction m as [| x xs]; intros. 
    - now simpl.
    - simpl.
      rewrite IHxs.
      apply ins_merge_assoc. 
  Qed. 


  Function msort (m: list nat) {measure length m}:=
    match m with
      | [] => []
      | [x] => [x]
      | _ => let (m1, m2) := unapp_half m in
             merge ((msort m1), (msort m2))
    end. 
  Proof.
    - intros.
      unfold unapp_half in teq1.
      symmetry in teq1.
      name_term len_x_n_l0 (length (x::n::l0)) LEN.
      rewrite <- LEN in *.
      simpl in LEN.
      assert (L0: len_x_n_l0 > 0) by omega.
      apply lt_div2 in L0.
      assert (len_x_n_l0 - div2 len_x_n_l0 > 0) by (apply gt_minus; auto).
      symmetry in teq1.
      apply unapp_reduce_m2 in teq1; auto.
      simpl in teq1.
      rewrite <- LEN in *.
      apply teq1.
      simpl.
      auto with arith.
    - intros. 
      unfold unapp_half in teq1.
      apply unapp_reduce_m1 in teq1.
      apply teq1. clear teq1.
      name_term len_x_n_l0 (length (x::n::l0)) LEN.
      rewrite <- LEN in *.
      simpl in LEN.
      assert (L0: len_x_n_l0 > 0) by omega.
      apply lt_div2 in L0.
      assert (L1: len_x_n_l0 > 1) by omega.
      rewrite LEN at 2.
      simpl.
      omega. 
  Defined. 




  
  Lemma isort_homomorphism: 
    forall m m1 m2,  
      (m1, m2) = unapp_half m -> 
      merge ((isort_seed [] m1), (isort_seed [] m2)) = 
      isort_seed [] (m1 ++ m2). 
  Proof. 
    intros * SP. 
    name_term lhs (merge ((isort_seed [] m1), (isort_seed [] m2))) LHS.
    rewrite <- LHS.
    rewrite isort_seed_inclusion.
    rewrite isort_seed_slideout. 
    now subst lhs.
  Qed. 

  
  Theorem isort__msort: 
    forall m, 
      isort m = msort m.
  Proof. 
    intro m.
    rewrite isort__isort_seed. 
    assert (exists k, length m <= k) 
      as [k K] by (exists (length m); auto). 
    revert m K.
    induction k as [| k]; intros * K.
    - assert (A1: length m = 0) by omega. 
      apply length_zero_iff_nil in A1.
      now subst m.
    - destruct m as [| x1 xs]. now simpl.
      destruct xs as [| x2 xs]. now simpl.
      rewrite msort_equation. 
      name_term tpl (unapp_half (x1::x2::xs)) Tpl;
        rewrite <- Tpl; destruct tpl as [m1 m2].
      simpl in K. 
      assert (K': S (length xs) <= k) by (rewrite le_S_n; auto); 
        clear K; rename K' into K.
      assert (length m1 <= length (x2::xs) 
              /\ length m2 <= length (x2::xs))
        as [A1 A2]. {
        symmetry in Tpl.
        apply unapp_half_nonnil_reduces in Tpl; auto.
        2: simpl; omega. 
        simpl in *.
        omega. 
      }
      simpl in A1, A2.
      assert (A3: length m1 <= k) by omega; clear A1.
      assert (A4: length m2 <= k) by omega; clear A2. 
      rewrite <- (IHk m1 A3); rewrite <- (IHk m2 A4).      
      rewrite isort_homomorphism with (m:=(x1::x2::xs)); auto.
      apply unapp_half_app in Tpl.
      now rewrite Tpl. 
  Qed. 


  
  Definition merge_op (m1 m2: list nat) := merge (m1, m2).

  Lemma Associative: 
    forall m1 m2 i,
      ins i (merge_op m1 m2) = merge_op (ins i m1) m2.
    unfold merge_op.
    apply ins_merge_assoc.
  Qed. 

  Check SplitPred.
  
  Lemma Recursive_Retention_L:
    forall (m1 m2: list nat),
      SplitPred m1 m2 ->
      forall x xs,
        m1 = x::xs ->
        SplitPred xs m2.      
  Proof.
    intros. 
    unfold SplitPred.
    trivial.
  Qed.
    


  Lemma isort_seed_inclusion_tac: 
    forall m1 m2 seed, 
      SplitPred m1 m2 -> 
      isort_seed seed (m1 ++ m2) 
      = isort_seed (isort_seed seed m2) m1.
  Proof.
    Unset Ltac Debug.
    linU_inclusion_tac
        isort_seed
        isort_seed_equation
        Base_Omitted
	Recursive_Retension_R
        idtac
        SplitPred
        Recursive_Retention_L
    . 
  Qed.
  
  Lemma Unit: forall seed,
      seed = merge_op [] seed.
  Proof. 
    intros. unfold merge_op.
    rewrite merge_equation.
    trivial.
  Qed.
  
  Lemma isort_seed_slideout_tac: 
    forall m seed, 
      isort_seed seed m
      = merge_op (isort_seed [] m) seed.
  Proof. 
    Unset Ltac Debug. 
    linU_slideout_tac
      isort_seed
      isort_seed_equation
      merge_op 
      Unit
      Associative
    .     
  Qed. 

  Lemma isort_homomorphism_tac: 
    forall m1 m2,  
      SplitPred m1 m2 -> 
      isort_seed [] (m1 ++ m2) = 
        merge_op (isort_seed [] m1) (isort_seed [] m2).
  Proof. 
    Unset Ltac Debug. 
    linU_homomorphism_tac
      isort_seed_equation

      Base_Omitted
      Recursive_Retension_R
      idtac
      Recursive_Retention_L
      
      Unit
      Associative
    .     
  Qed.


  Theorem isort__msort_tac: 
    forall m, 
      isort m = msort m.
  Proof. 
    intro.
    rewrite isort__isort_seed.
    functional induction (msort m); auto.
    cut (SplitPred m1 m2). 2: (unfold SplitPred; trivial). intro SP.    
    apply isort_homomorphism_tac in SP.
    unfold merge_op in SP. rewrite IHl in SP. rewrite IHl0 in SP.
    symmetry in e0. apply unapp_half_app in e0. subst m.
    apply SP.
  Qed.


  
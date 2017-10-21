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
    
    Hypothesis second_duality_thm_1: 
      forall x y z,
        cr x (cl y z) = 
        cl (cr x y) z.
    
    Hypothesis second_duality_thm_2:
      forall x, 
        cr x e = cl e x. 
    
    Lemma cr_carried_over_fold_left: 
      forall l i acc, 
        cr i (fold_left cl l acc) = fold_left cl l (cr i acc). 
    Proof. 
      intro.
      induction l as [| x xs]; intros.
      - unfold fold_left.
        reflexivity.
      - simpl.
        rewrite IHxs.
        rewrite <- second_duality_thm_1.
        reflexivity.        
    Qed.       
    
    Lemma fold_right_cr__fold_left_cl:
      forall l, 
        (fold_right cr) e l = (fold_left cl) l e.
    Proof.
      intro. 
      induction l as [| x xs]; simpl.
      - reflexivity.
      - rewrite IHxs.
        rewrite cr_carried_over_fold_left. 
        rewrite second_duality_thm_2. 
        reflexivity.
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
      intros. 
      induction m as [| x xs].
      - simpl.
        symmetry.
        apply Unit.
      - simpl.
        rewrite <- Associative. 
        rewrite IHxs.
        reflexivity.
        
    Restart.
        
    linU_slideout_tac
      cata_seed
      cata_seed_equation
      binop
      Unit
      Associative.
    Qed.    

    
    Variable f: A -> B.

    Variable h: list A -> B.
      
    Hypothesis List_Homomorphism:
      h [] = e /\
      forall a, h [a] = f a /\
      forall m1 m2,
        h (m1 ++ m2) = binop (h m1) (h m2).

    Hypothesis split: list A -> (list A * list A).
    Hypothesis split_pred: forall m m1 m2,
        split m = (m1,m2) -> m = m1 ++ m2.

          
          
  End Dual_cata.
    

  Section Rev. 
    Context { A: Type }.

    Definition cr_rev (k: A) (acc: list A) := acc ++ [k].
    Definition cl_rev (acc: list A) (k: A) := k :: acc.

    Definition rev_r (m: list A) := fold_right cr_rev [] m.

    Lemma rev__rev_r : 
      forall (m: list A),
        rev m = rev_r m. 
    Proof. 
      intros. 
      unfold rev_r.
      induction m as [| x xs]; simpl.
      - reflexivity. 
      - unfold cr_rev at 1.
        rewrite IHxs.
        reflexivity. 
    Qed.
    
    Definition rev_l (m: list A) := fold_left cl_rev m [].

    Lemma second_duality_thm_1: 
      forall (x: A) (y: list A) (z: A),
        cr_rev x (cl_rev y z) = cl_rev (cr_rev x y) z.
    Proof. 
      intros. 
      unfold cl_rev, cr_rev.
      simpl.
      reflexivity.
    Qed.
    

    Lemma second_duality_thm_2:
      forall (x: A), 
        cr_rev x ([]: list A) = cl_rev ([]: list A) x. 
    Proof. 
      intros.
      simpl.
      reflexivity.
    Qed.
  

    Lemma rev_r__rev_l: 
      forall (m: list A),
        rev_r m = rev_l m.
    Proof. 
      intros. 
      unfold rev_l, rev_r.
      apply fold_right_cr__fold_left_cl; auto.
    Qed. 
    
    
    Fixpoint rev_tr (m acc: list A): list A :=
      match m with
        | [] => acc
        | (x::xs) => rev_tr xs (x::acc) 
      end. 
       
    Lemma fold_left_cl_rev___rev_tr: 
      forall (m acc: list A), 
        fold_left cl_rev m acc = rev_tr m acc.
    Proof.
      intro m.
      unfold rev_l.
      induction m as [| x xs]; intro; simpl.
      - reflexivity.
      - rewrite IHxs.
        unfold cl_rev.
        reflexivity.
    Qed.         

    Theorem rev_l__rev_tr: 
      forall (m acc: list A), 
        rev_l m = rev_tr m [].
    Proof.
      unfold rev_l.
      intros.
      apply fold_left_cl_rev___rev_tr.
    Qed. 
        
        
    Theorem rev__rev_tr : 
      forall (m: list A),
        rev m = rev_tr m []. 
    Proof. 
      intros. 
      rewrite rev__rev_r.
      rewrite rev_r__rev_l.
      apply rev_l__rev_tr.
      apply m.
    Qed.
         
    
  End Rev.


  Section Map. 
    Context {A B: Type}.
    Context {f: A -> B}.
    
    Definition cr_map (k: A) (acc: list B) := (f k) :: acc.
    Definition cl_map (acc: list B) (k: A) := acc ++ [f k].


    Definition map_r (m: list A): list B := fold_right cr_map [] m.
    Definition map_l (m: list A): list B := fold_left cl_map m [].

    Definition map_r_seed (seed: list B) (m: list A): list B := fold_right cr_map seed m.
    Definition map_l_acc (acc: list B) (m: list A): list B := fold_left cl_map m acc.

    Fixpoint map_tr_aux (acc: list B) (m: list A): list B:= 
      match m with 
        | [] => acc
        | x::xs => map_tr_aux (acc ++ [f x]) xs
      end.
    Definition map_tr (m: list A) := map_tr_aux [] m.


    (**
<<
         map   
          |    
          |  map__map_r  
          |    
         map_r 
          | 
          |  map_r__map_l
          | 
         map_l ---------------------+
          |                         |
          |  map_l__map_l_acc       |
          |                         |
         map_l_acc                  |  map_tr__map_l
          |                         |
          |  map_tr_aux__map_l_acc  |
          |                         |
         map_tr_aux                 |
          |                         |
          +-------------------------+
          |
         map_tr  

>>

*)
    Lemma map__map_r: 
      forall (m: list A),
        map f m = map_r m.
    Proof. 
      induction m as [| x xs];
      unfold map_r.
      - now simpl.
      - simpl.
        rewrite IHxs.
        unfold map_r. 
        unfold cr_map at 2.
        reflexivity.
    Qed.

    Lemma map_r__map_l: 
      forall (m: list A),
        map_r m = map_l m.
    Proof. 
      intros. 
      unfold map_l, map_r.
      apply fold_right_cr__fold_left_cl; auto. 
    Qed. 

    Lemma map_l__map_l_acc:
      forall m, 
      map_l m = map_l_acc [] m. 
    Proof. 
      intros. 
      now unfold map_l; unfold map_l_acc.
    Qed. 


    Lemma map_tr_aux__map_l_acc: 
      forall (m: list A) (acc: list B),
        map_tr_aux acc m = map_l_acc acc m.
    Proof.
      intro m.
      induction m as [| x xs]; intro acc.
      - unfold map_l_acc; unfold list_id.
        now simpl.
      - simpl.
        unfold map_l_acc; unfold list_id.
        rewrite IHxs.
        unfold map_l_acc; unfold cl_map; fold cl_map; unfold list_id.
        reflexivity.
    Qed. 
        
    Lemma map_tr__map_l: 
      forall (m: list A),
        map_tr m = map_l m.
    Proof. 
      intro m.
      unfold map_tr.
      rewrite map_l__map_l_acc.
      apply map_tr_aux__map_l_acc.
    Qed. 

    Theorem map__map_tr: 
      forall (m: list A),
        map f m = map_tr m.
    Proof. 
      intro m.
      rewrite map_tr__map_l.
      rewrite map_l__map_l_acc.
      rewrite <- map_r__map_l.
      apply map__map_r.
    Qed. 
  End Map.


  Section Filter. 
    Context {A: Type}.
    Context {f: A -> bool}.
    
    Definition cr_filter (k: A) (acc: list A) := if f k then k :: acc
                                                 else acc.
    
    Definition cl_filter (acc: list A) (k: A) := if f k then acc ++ [k]
                                                 else acc.
    

    Lemma filter_second_duality_thm_1: 
      forall (x: A) (y: list A) (z: A),
        cr_filter x (cl_filter y z) = cl_filter (cr_filter x y) z.
    Proof. 
      intros. 
      unfold cl_filter, cr_filter.
      remember (f x) as rx.
      remember (f z) as rz.
      destruct rx; destruct rz; auto.
    Qed.


    Definition filter_r (m: list A) := fold_right cr_filter [] m.
    Definition filter_l (m: list A) := fold_left cl_filter m [].

    Definition filter_r_seed (seed: list A) (m: list A) :=
      fold_right cr_filter seed m.
    Definition filter_l_acc (acc: list A) (m: list A) :=
      fold_left cl_filter m acc.

    Print filter. 

    Fixpoint filter_tr_aux (acc: list A) (m: list A) :=
      match m with 
        | [] => acc
        | x::xs => let acc := if f x then (acc ++ [x])
                              else acc
                   in filter_tr_aux acc xs
      end.
    Definition filter_tr (m: list A) := filter_tr_aux [] m.


    (**

<<
        filter 
          | 
          |  filter__filter_r
          |
        filter_r
          | 
          |  filter_r__filter_l
          | 
        filter_l ------------------------+
          |                              |
          |  filter_l__filter_l_acc      |
          |                              |
        filter_l_acc                     |  filter_l__filter_tr
          |                              |
          |  filter_l_acc__map_tr_aux    |
          |                              |
        filter__tr_aux                   |
          |                              |
          +------------------------------+
          |
        filter_tr


>>

     *)
    
    
    Lemma filter_r__filter_l: 
      forall (m: list A),
        filter_r m = filter_l m.
    Proof. 
      intros. 
      unfold filter_l, filter_r.
      apply fold_right_cr__fold_left_cl; auto.
      apply filter_second_duality_thm_1.
    Qed. 

    Lemma filter__filter_r:
      forall (m: list A),
        filter f m = filter_r m.
    Proof.     
      induction m as [| x xs].
      - unfold filter_r.
        now simpl.
      - simpl.
        unfold filter_r.
        unfold cr_filter.
        fold cr_filter. 
        rewrite IHxs.
        unfold filter_r.
        remember (f x) as r.
        destruct r; auto.
    Qed. 

    Lemma filter_l__filter_l_acc: 
      forall m,
        filter_l m = filter_l_acc [] m.
    Proof. 
      intro.
      now unfold filter_l; unfold filter_l_acc.
    Qed.


    Lemma filter_l_acc__map_tr_aux: 
      forall m acc,
        filter_l_acc acc m = filter_tr_aux acc m. 
    Proof. 
      intro m.
      induction m as [| x xs]; intro acc.
      - unfold filter_l_acc.
        now simpl.
      - simpl.
        rewrite IHxs.
        unfold cl_filter.
        reflexivity.
    Qed. 

    Lemma filter_l__filter_tr: 
      forall m,
        filter_l m = filter_tr m.
    Proof.
      intro m.
      unfold filter_tr.
      rewrite <- filter_l_acc__map_tr_aux.
      apply filter_l__filter_l_acc.
    Qed.

    Theorem filter__filter_tr:
      forall m, 
        filter f m = filter_tr m.
    Proof. 
      intro m.
      rewrite filter__filter_r.
      rewrite filter_r__filter_l.
      apply filter_l__filter_tr.
    Qed.

  End Filter. 

  (*
  Section Dual_hylo.

    Fixpoint binop (m1: list A) (m2: B) :=
      match m1 with
        | [] => m2
        | x::xs => cr x (binop xs m2)
      end. 

    Parameter g_nil: g [] = [].
    *)
    




  Section Sum. 
    Context {f: nat -> nat -> nat}.

    Definition cr_sum (k: nat) (acc: nat) := k + acc.
    
    Definition cl_sum (acc: nat) (k: nat) := acc + k.

    Lemma sum_second_duality_thm_1: 
      forall (x: nat) (y: nat) (z: nat),
        cr_sum x (cl_sum y z) = cl_sum (cr_sum x y) z.
    Proof. 
      intros. 
      unfold cl_sum, cr_sum.
      omega. 
    Qed.

    Definition sum_r (m: list nat) := fold_right cr_sum O m.
    Definition sum_l (m: list nat) := fold_left cl_sum m O.

    Definition sum_r_seed (seed: nat) (m: list nat) :=
      fold_right cr_sum seed m.
    
    Definition sum_l_acc (acc: nat) (m: list nat) :=
      fold_left cl_sum m acc.

    Print sum. 

    Fixpoint sum_tr_aux (acc: nat) (m: list nat) :=
      match m with 
        | [] => acc
        | x::xs => sum_tr_aux (acc + x) xs
      end.
    Definition sum_tr (m: list nat) := sum_tr_aux O m.


    (**

<<
        sum 
          | 
          |  sum__sum_r
          |
        sum_r
          | 
          |  sum_r__sum_l
          | 
        sum_l ------------------------+
          |                           |
          |  sum_l__sum_l_acc         |
          |                           |
        sum_l_acc                     |  sum_l__sum_tr
          |                           |
          |  sum_l_acc__map_tr_aux    |
          |                           |
        sum__tr_aux                   |
          |                           |
          +---------------------------+
          |
        sum_tr


>>

     *)
    
    
    Lemma sum_r__sum_l: 
      forall (m: list nat),
        sum_r m = sum_l m.
    Proof. 
      intros. 
      unfold sum_l, sum_r.
      apply fold_right_cr__fold_left_cl; auto.
      apply sum_second_duality_thm_1.
    Qed. 


    Lemma sum_l__sum_l_acc: 
      forall m,
        sum_l m = sum_l_acc 0 m.
    Proof. 
      intro.
      now unfold sum_l; unfold sum_l_acc.
    Qed.


    Lemma sum_l_acc__map_tr_aux: 
      forall m acc,
        sum_l_acc acc m = sum_tr_aux acc m. 
    Proof. 
      intro m.
      induction m as [| x xs]; intro acc.
      - unfold sum_l_acc.
        now simpl.
      - simpl.
        rewrite IHxs.
        reflexivity.
    Qed. 

    Lemma sum_l__sum_tr: 
      forall m,
        sum_l m = sum_tr m.
    Proof.
      intro m.
      unfold sum_tr.
      rewrite <- sum_l_acc__map_tr_aux.
      apply sum_l__sum_l_acc.
    Qed.
    

    (*
    Theorem sum__sum_tr:
      forall m, 
        sum f m = sum_tr m.
    Proof. 
      intro m.
      rewrite sum__sum_r.
      rewrite sum_r__sum_l.
      apply sum_l__sum_tr.
    Qed.
     *)

  End Sum. 




  Section Len. 
    Context {A: Type}.

    Definition cr_len (k: A) (acc: nat) := S acc.
    Definition cl_len (acc: nat) (k: A) := S acc.

    Lemma len_second_duality_thm_1: 
      forall (x: A) (y: nat) (z: A),
        cr_len x (cl_len y z) = cl_len (cr_len x y) z.
    Proof. 
      intros. 
      unfold cl_len, cr_len.
      omega. 
    Qed.

    Definition len_r (m: list A) := fold_right cr_len O m.
    Definition len_l (m: list A) := fold_left cl_len m O.

    Definition len_r_seed (seed: nat) (m: list A) :=
      fold_right cr_len seed m.
    
    Definition len_l_acc (acc: nat) (m: list A) :=
      fold_left cl_len m acc.

    Fixpoint len (m: list A) :=
      match m with
        | [] => O
        | x::xs => S (len xs)
      end.


    Fixpoint len_tr_aux (acc: nat) (m: list A) :=
      match m with 
        | [] => acc
        | x::xs => len_tr_aux (S acc) xs
      end.
    Definition len_tr (m: list A) := len_tr_aux O m.


    (**

<<
        len 
          | 
          |  len__len_r
          |
        len_r
          | 
          |  len_r__len_l
          | 
        len_l ------------------------+
          |                           |
          |  len_l__len_l_acc         |
          |                           |
        len_l_acc                     |  len_l__len_tr
          |                           |
          |  len_l_acc__map_tr_aux    |
          |                           |
        len__tr_aux                   |
          |                           |
          +---------------------------+
          |
        len_tr


>>

     *)
    
    
    Lemma len_r__len_l: 
      forall (m: list A),
        len_r m = len_l m.
    Proof. 
      intros. 
      unfold len_l, len_r.
      apply fold_right_cr__fold_left_cl; auto.
    Qed. 

    Lemma len_l__len_l_acc: 
      forall m,
        len_l m = len_l_acc 0 m.
    Proof. 
      intro.
      now unfold len_l; unfold len_l_acc.
    Qed.

    Lemma len_l_acc__map_tr_aux: 
      forall m acc,
        len_l_acc acc m = len_tr_aux acc m. 
    Proof. 
      intro m.
      induction m as [| x xs]; intro acc.
      - unfold len_l_acc.
        now simpl.
      - simpl.
        rewrite IHxs.
        reflexivity.
    Qed. 

    Lemma len_l__len_tr: 
      forall m,
        len_l m = len_tr m.
    Proof.
      intro m.
      unfold len_tr.
      rewrite <- len_l_acc__map_tr_aux.
      apply len_l__len_l_acc.
    Qed.

    Lemma len__len_r: 
      forall m,
        len m = len_r m.
    Proof.
      induction m as [| x xs]; simpl.
      - reflexivity.
      - rewrite IHxs.
        unfold cr_len.
        reflexivity.
    Qed.

    Theorem len__len_tr:
      forall m, 
        len m = len_tr m.
    Proof. 
      intro m.
      rewrite len__len_r.
      rewrite len_r__len_l.
      apply len_l__len_tr.
    Qed.


  Lemma len_S: forall (m: list A) (n: nat) (i: A), 
                 len m = n -> len (i::m) = S n.
  Proof.
    intros.
    simpl.
    auto.
  Qed.

  
  Lemma len_tr_S: 
    forall (m: list A) (n: nat) (i: A), 
      len_tr m = n -> len_tr (i::m) = S n.
  Proof.
    intros * L.
    rewrite <- len__len_tr in *.
    now apply len_S.
  Qed.


  
  Lemma len_GeGt_hd: 
    forall (m: list A) (n: nat) (i: A), 
      len m >= n -> len (m ++ [i]) > n.
  Proof.
    induction m as [| x xs]; intros * H; simpl in *; try omega. 
    destruct n as [| n']; try omega. 
    apply le_S_n in H.
    apply IHxs with (i:=i) in H.
    omega. 
  Qed.
  
  Lemma len_GeGt_end: 
    forall (m: list A) (n: nat) (i: A), 
      len m >= n -> len (i::m) > n.
  Proof.
    simpl.
    intros.
    omega.
  Qed.


  Lemma len_tr_aux_GeGt_hd: 
    forall (m: list A) (n: nat) (i: A), 
    (forall (k: nat), len_tr_aux k m >= k + n) 
    -> forall (k': nat), len_tr_aux k' (i::m) > k' + n.
  Proof.
    intros * L *.
    simpl.
    apply le_trans with (m:=S k' + n); auto.
    specialize (L (S k')).
    auto.
  Qed.
  

  End Len. 



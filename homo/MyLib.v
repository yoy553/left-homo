
  Require Export ZArith. 
  Require Export NPeano.

  Require Export List. 
  Export ListNotations.

  Require Import Sorting.Sorted.


  Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).  

(** Start with blank

 *)


  Ltac name_term n t H := 
    assert (H: exists n', n' = t);
      try (exists t; reflexivity);
      destruct H as [n H]. 


  Require Import Coq.Arith.Wf_nat.                 (* [lt_wf] *)
  Require Import Coq.Wellfounded.Inverse_Image.    (* [wf_inverse_image] *)

  Section ListLen. 
    Context { A: Type }.
    Definition lt_length (m1 m2: list A) := length m1 < length m2. 
    Lemma lt_length_wf: well_founded lt_length. 
    Proof.
      unfold lt_length. 
      eapply wf_inverse_image. eapply lt_wf.
    Defined.
  End ListLen.

  
  Section ListId. 
    Context {A: Type}.

    Definition list_id (l: list A) := l.

    Lemma list_id_wont_expand: 
      forall (l_in l_out: list A), 
        l_out = list_id l_in -> length l_out <= length l_in.
      intros l_in l_out H. 
      unfold list_id in H.
      subst; auto.
    Qed.
    
    Lemma id_lt: 
      forall m (x: A) xs, 
        list_id m = (x::xs) -> lt_length xs m. 
    Proof. 
      intros.
      unfold list_id in H.
      subst m.
      unfold lt_length.
      auto.
    Qed.  
  End ListId.
  
  Section ListOption. 
    Context {A: Type}.

    Definition list_option (l: list A) := 
      match l with 
        | [] => None
        | x :: xs => Some (x, xs)
      end.

    Lemma list_option_wont_expand: 
      forall (l_in l_out: list A) x o_out, 
        o_out = list_option l_in -> 
        o_out = None \/ 
        (o_out = Some (x, l_out) -> length l_out <= length l_in).
      intros l_in l_out * H. 
      unfold list_option in H.
      destruct l_in as [| y ys].
      - left; apply H.
      - right; intro O; rewrite H in O; injection O; intros Ys Y.
        subst; auto.
        simpl; auto with arith.
    Qed.
    
    Lemma list_option_lt: 
      forall m (x: A) l, 
        list_option m = Some (x, l) -> lt_length l m. 
    Proof. 
      intros.
      unfold list_option in H.
      destruct m as [| y ys].
      - inversion H. 
      - injection H; intros Ys Y.
        subst; auto.
        unfold lt_length.
        simpl; auto with arith.
    Qed.  
  End ListOption.



  Section UnApp.
    Context {A: Type}.

    Fixpoint unapp (n:nat)(m:list A) : list A * list A:=
      match n with
        | 0 => ([], m)
        | S n => match m with
                   | nil => ([], [])
                   | x::xs => let (m1, m2) := unapp n xs in
                              (x::m1, m2)
                 end
      end.

    Lemma unapp_wont_expand: 
      forall n (m m1 m2: list A), 
        unapp n m = (m1, m2) -> 
        length m1 <= length m /\ length m2 <= length m. 
    Proof. 
      induction n as [| n]; intros * UA. 
      - simpl in UA. injection UA; intros M1 M2.
        subst m1 m2. auto with arith.
      - destruct m. 
        + simpl in UA.
          injection UA; intros M1 M2. 
          subst m1 m2. auto with arith. 
        + simpl in UA.
          name_term ua' (unapp n m) UA'.
          rewrite <- UA' in UA.
          destruct ua' as [m1' m2'].
          injection UA; intros M1 M2; subst m1 m2; clear UA.
          symmetry in UA'.
          apply IHn in UA'.
          simpl.
          omega. 
    Qed.        
    
    Lemma unapp_app: 
      forall n (m m1 m2: list A),
        (m1, m2) = unapp n m -> 
        m1 ++ m2 = m.
    Proof. 
      intros n m.
      revert n.
      induction m as [| x xs]; intros * UA.
      - destruct n as [| n'];
        simpl in UA;
        injection UA; intros M1 M2; subst m1 m2; clear UA;
        simpl; auto with arith.
      - destruct n as [| n'];
        simpl in UA.
        + injection UA; intros M1 M2; subst m1 m2; clear UA.
          reflexivity.
        + name_term ua' (unapp n' xs) UA'.  rewrite <- UA' in UA.
          destruct ua' as [m1' m2'].
          injection UA; intros M1 M2; subst m1 m2; clear UA.
          simpl. 
          apply IHxs in UA'.
          subst xs.
          reflexivity.
    Qed. 

    Lemma unapp_reduce_m1: 
      forall n (m m1 m2: list A), 
        unapp n m = (m1, m2) -> 
        n < length m -> 
        length m1 < length m. 
    Proof. 
      intros n m. 
      revert n.
      induction m as [| x xs];
        intros * UA NltM. 
      - simpl in NltM. inversion NltM.
      - destruct n as [| n].
        + unfold unapp in UA.
          injection UA; intros M1 M2; subst m1 m2; clear UA.
          simpl. auto with arith.
        + simpl in UA.
          simpl in NltM. 
          apply lt_S_n in NltM.
          name_term ua' (unapp n xs) UA'.  rewrite <- UA' in UA.
          destruct ua' as [m1' m2'].
          injection UA; intros M1 M2; subst m1 m2; clear UA.
          symmetry in UA'.
          apply IHxs in UA'; auto.
          simpl.
          omega. 
    Qed. 


    Lemma unapp_reduce_m2: 
      forall n (m m1 m2: list A), 
        unapp n m = (m1, m2)-> 
        n > 0 ->
        length m > 0 -> 
        length m2 < length m. 
    Proof. 
      intros * UA Ngt0 Mgt0. 
      cut (length m1 > 0). 
      {
        intro H.
        symmetry in UA.
        apply unapp_app in UA.
        subst m.
        rewrite app_length in *.
        omega. 
      }
      destruct n as [| n']; destruct m as [| x xs].
      - inversion Ngt0.
      - inversion Ngt0.
      - simpl in Mgt0.
        inversion Mgt0.      
      - simpl in UA.
        name_term ua' (unapp n' xs) UA'.  rewrite <- UA' in UA.
        destruct ua' as [m1' m2'].
        injection UA; intros M1 M2; subst m1 m2; clear UA.
        simpl. auto with arith.
    Qed. 


  End UnApp.

  Require Export Div2.
  Lemma div2_SS: 
    forall n, div2 (S (S n)) > 0.
  Proof. 
    induction n; simpl; auto with arith.
  Qed. 

  Lemma le_div2: 
    forall n, n >= div2 n.
  Proof.
    intro n.
    destruct n as [| n]; auto. 
    cut (S n > div2 (S n)).
    intro C; auto with arith.
    apply lt_div2; auto with arith.
  Qed.

  Section UnappHalf.
    Context {A: Type}.

    Definition unapp_half(m: list A) :=
      let n := length m in 
      let n2 := div2 n in
      let n1 := n - n2 in
      unapp n1 m. 
    
    Lemma unapp_half_app: 
      forall m m1 m2,
        (m1, m2) = unapp_half m -> 
        m1 ++ m2 = m.
    Proof. 
      induction m as [| x xs]; intros * SP. 
      inversion SP; auto.
      unfold unapp_half in SP.
      apply unapp_app in SP.
      auto.
    Qed. 
    
    Lemma unapp_half_nonnil_reduces: 
      forall m m1 m2, 
        unapp_half m = (m1,m2) -> 
        length m > S 0 -> 
        length m1 < length m /\ length m2 < length m.
    Proof. 
      intros * SP MgtO.
      unfold unapp_half in SP.
      name_term k (length m) LEN. 
      rewrite <- LEN in *.
      name_term n (k - div2 k) N1. 
      rewrite <- N1 in SP.     
      assert (DK: div2 k < k) 
        by (apply lt_div2; auto with arith).
      name_term d (div2 k) D. 
      rewrite <- D in *.
      destruct m as [| x1 xs]. 
      simpl in LEN. subst k. inversion DK.
      destruct xs as [| x2 xs].
      simpl in LEN. subst k. inversion MgtO. inversion H0.
      assert (DgtO: d > 0) by (subst k d; apply div2_SS). 
      assert (NltM: n < length (x1::x2::xs))
        by (simpl in *; omega). 
      subst k.
      split. 
      - apply unapp_reduce_m1 with (n0:=n) (m4:=m2); auto.
      - assert (n > 0) by omega. 
        assert (length (x1::x2::xs) > 0) by (simpl; omega).
        apply unapp_reduce_m2 with (n0:=n) (m3:=m1); auto.
    Qed. 

    Lemma unapp_half_wont_expand: 
      forall m m1 m2, 
        unapp_half m = (m1,m2) -> 
        length m1 <= length m /\ length m2 <= length m.
    Proof. 
      intros * SP. 
      unfold unapp_half in SP.
      apply unapp_wont_expand with (n:=length m - div2 (length m)); auto.
    Qed. 

  End UnappHalf.

  Lemma tuple_eq : 
    forall {A B: Type} (x a: A) (y b: B), 
      x = a /\ y = b <-> (x,y) = (a,b). 
  Proof. 
    intros.
    split.
    - intros [L R]; now subst.
    - intro H; now inversion H.
  Qed.       

  Lemma gt_minus: 
    forall x y, 
      x > y -> x - y > 0.
  Proof. 
    induction x; intros * GT. 
    - inversion GT.
    - destruct y. 
      + auto with arith.
      + apply gt_S_n in GT.
        apply IHx in GT.
        auto with arith.
  Qed. 


  Lemma nil_f_nil: 
    forall (A B: Type) (f: list A -> list B),
      (forall l, length (f l) <= length l) -> 
      f [] = [].
  Proof. 
    intros A B f PF.
    name_term f_out (f []) F.
    destruct f_out as [| x xs]. 
    - auto.
    - assert (length (f []) <= length ([]: list A)) as A1. 
      {
        apply PF.
      }
      rewrite <- F in A1.
      simpl in A1.
      inversion A1.
  Qed.



  Lemma rev_inv:
    forall (X: Type) (l m: list X), 
      rev l = m ->
      rev m = l. 
  Proof. 
    intros X l m L.
    subst m.
    apply rev_involutive.     
  Qed.     
  

(** To add a new reference cell to the store, we use [snoc]. *)
  Fixpoint snoc {A:Type} (l:list A) (x:A) : list A :=
    match l with
    | nil    => x :: nil
    | h :: t => h :: snoc t x
    end.
  

  (**
     from Poly.v
     *)
  Theorem rev_snoc : forall X : Type, 
    forall v : X,
      forall s : list X,
        rev (snoc s v) = v :: (rev s).
  Proof. 
    intros X v s. induction s as [|h t]. reflexivity. 
    simpl. rewrite -> IHt.
    simpl. reflexivity. Qed. 
  
  
  Lemma length_snoc : forall A (l:list A) x,
      length (snoc l x) = S (length l).
  Proof.
    induction l; intros; [ auto | simpl; rewrite IHl; auto ]. Qed.
  
  (* The "solve by inversion" tactic is explained in Stlc.v. *)
  Lemma nth_lt_snoc : forall A (l:list A) x d n,
      n < length l ->
      nth n l d = nth n (snoc l x) d.
  Proof.
    induction l as [|a l']; intros.
    inversion H. 
    destruct n; auto.
    simpl. apply IHl'. 
    simpl in H. apply lt_S_n in H. assumption.
  Qed.
  
  Lemma nth_eq_snoc : forall A (l:list A) x d,
      nth (length l) (snoc l x) d = x.
  Proof.
    induction l; intros; [ auto | simpl; rewrite IHl; auto ].
  Qed.
  
  Lemma nth_i_nil__default: forall (A: Type) (i: nat) (d: A),
    nth i [] d = d. 
  Proof. 
    intros A i d.
    induction i as [| i'].
    simpl. auto.
    simpl. auto.
  Qed.


  Lemma snoc_list: forall X: Type, forall y: X, forall l: list X,
          snoc l y = l ++ [y].
  Proof. intros X y l. induction l as [|x xs]. 
         reflexivity.
         simpl. rewrite -> IHxs. reflexivity. Qed.
  
  
  Theorem snoc_with_append : forall X : Type, 
      forall l1 l2 : list X,
      forall v : X,
        snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
    intros X l1 l2 v. induction l2 as [|x xs].
    simpl. 
    assert (l1 ++ [] = l1 ) as H.
    rewrite app_nil_r. reflexivity. rewrite H.
    rewrite snoc_list. reflexivity.     
    simpl.
    rewrite snoc_list. 
    rewrite snoc_list. 
    rewrite <- app_assoc. reflexivity. Qed.



  Theorem snoc_with_tail : forall X : Type, 
                         forall l : list X,
                         forall h v : X,
    snoc (h::l) v = h :: (snoc l v).
  Proof.
    intros X l h v. 
    simpl.
    reflexivity.
  Qed.

  
  Lemma snoc__eq__snoc: forall (X: Type) (x y: X) (xs ys: list X),
    snoc xs x = snoc ys y <-> xs = ys /\ x = y.
  Proof.
    intros. 
    split.
    - intro H.
      split.
      + generalize dependent ys. 
        induction xs as [| xh xt]; intros ys H. 
        * induction ys as [| yh yt]. inversion H. auto.
          inversion H. destruct yt. inversion H2. inversion H2.
        * induction ys as [| yh yt]. inversion H. 
          destruct xt. inversion H2. inversion H2.
          
          simpl in H.
          inversion H.
          apply IHxt in H2.
          now subst.
      + generalize dependent ys. 
        induction xs as [| xh xt]; intros ys H. 
        * induction ys as [| yh yt]. inversion H. auto.
          inversion H. destruct yt. inversion H2. inversion H2.
        * induction ys as [| yh yt]. inversion H. 
          destruct xt. inversion H2. inversion H2.
          simpl in H.
          inversion H.

          rewrite IHxt with (ys:=yt); auto.
    - intros [Hxs Hx].
      now subst.
  Qed.


  Lemma snoc_l_eqv: forall (X: Type) (l m: list X) (r: X), 
    snoc l r = snoc m r <-> l = m.
  Proof.
    intros.
    split; intro H;
      try apply snoc__eq__snoc in H. 
    destruct H as [H1 H2]. exact H1.
    subst l. reflexivity.
  Qed.
  
  Lemma list__ex_snoc: forall (X: Type) (l xs: list X) (x: X),
    l = (x::xs) -> exists l_front, exists l_end, l = (snoc l_front l_end). 
  Proof. 
    intros X l xs x H.
    generalize dependent x. 
    generalize dependent l. 
    induction xs as [| x' xs']; intros l x H.
    - exists []. exists x. simpl. auto.
    - induction l. inversion H.
      inversion H.

      assert (exists l_front : list X, exists l_end : X, l = snoc l_front l_end) as EX_FE.
        apply IHxs' with (x:=x'). auto.

      destruct EX_FE as [l_front' [l_end' SNC]].

      exists (x::l_front'). 
      exists l_end'.

      simpl. 
      rewrite <- SNC.
      rewrite <- H2.
      auto.
  Qed.


   Lemma list_cat__with_empty_front: forall (X:Type) (l1 l2: list X),
     l1 ++ l2 = l2 -> l1 = [].
   Proof.     
     intros X l1 l2 H.
     assert (l1 ++ l2 = [] ++ l2) as EQ.
     simpl. auto.
     apply app_inv_tail in EQ.
     rewrite EQ. 
     reflexivity.
   Qed.



  Definition eq_nat_tuple_dec : forall x y: nat * nat, 
                               {x = y} + {x <> y}.
  Proof. 
    intros x y.
    destruct x as [x1 x2]; destruct y as [y1 y2].

    remember (beq_nat x1 y1) as r1.
    remember (beq_nat x2 y2) as r2.
    destruct r1; destruct r2.    

    left. 
    apply beq_nat_eq in Heqr1.
    apply beq_nat_eq in Heqr2.
    subst. auto.

    right.
    intro cntr.
    apply beq_nat_eq in Heqr1.
    symmetry in Heqr2.
    apply beq_nat_false in Heqr2.
    subst.
    inversion cntr.
    apply Heqr2. auto.

    right.
    apply beq_nat_eq in Heqr2.
    symmetry in Heqr1.
    apply beq_nat_false in Heqr1.
    intro cntr.
    subst.
    inversion cntr.
    apply Heqr1. auto.

    right.
    intro cntr.
    symmetry in Heqr1.
    symmetry in Heqr2.
    apply beq_nat_false in Heqr1.
    apply beq_nat_false in Heqr2.
    inversion cntr.
    apply Heqr1.
    subst. auto.
  Qed.


  Lemma tuple_exmid: forall (x1 x2 y1 y2: nat),
    (x1,x2) = (y1,y2) \/ (x1,x2) <> (y1,y2). 
  Proof.
    intros.
    destruct (eq_nat_tuple_dec (x1,x2) (y1,y2));
    intuition.
  Qed.


  Fixpoint natInLst (n: nat) (l: list nat) : bool :=
    match l with
      | nil => false
      | x::xs => if beq_nat n x then true
                 else natInLst n xs
    end.

  Fixpoint lstSub_nat (lst_A: list nat) (lst_B: list nat) : list nat :=
    match lst_A with 
      | nil => []
      | x::xs => if natInLst x lst_B then lstSub_nat xs lst_B
                 else x::(lstSub_nat xs lst_B)
    end.

   Lemma lstSub_hd: forall rl i h t,
     h::t = lstSub_nat rl [i] ->
     h <> i.
   Proof.
     intro rl.
     induction rl as [| r rl']; intros i h t LS.
     - simpl in LS. inversion LS.
     - simpl in LS.
       remember (r =? i) as ri.
       destruct ri.
       + apply beq_nat_eq in Heqri.
         subst.
         apply IHrl' with (t:=t).
         auto.
       + inversion LS.
         subst.
         symmetry in Heqri.
         apply beq_nat_false in Heqri.
         auto.

  Qed.

   Require Export Bool. 
   
  (** From DeepSpec Summer School, Part29, Appel (July 24, 2017)    
   *)
  Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
  Proof.
    intros.
    apply iff_reflect.
    symmetry. apply Nat.leb_le.
  Qed.

  Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
  Proof.
    intros.
    apply iff_reflect.
    symmetry. apply Nat.eqb_eq.
  Qed.
  
  Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
  Proof.
    intros.
    apply iff_reflect.
    symmetry. apply Nat.ltb_lt.
  Qed.


   
   Fixpoint nat_in (n: nat) (l: list nat) : bool :=
     match l with 
     | nil => false
     | n'::l' => if n =? n' then true
                  else nat_in n l'
     end.

   Lemma nat_in__existsb: forall l n,
       nat_in n l = existsb (fun n' => n =? n') l. 
   Proof. 
     intro l. 
     induction l as [| x xs]; intro n; simpl.
     - reflexivity.
     - destruct (beq_reflect n x). 
       + subst n. 
         auto.
       + rewrite <- IHxs.
         auto.
   Qed.          

   Lemma In__nat_in: forall lst i,
       In i lst <-> nat_in i lst = true. 
   Proof.
     intros. 
     rewrite nat_in__existsb.
     split; intro H.
     - apply existsb_exists.
       exists i.
       split. apply H. 
       apply Nat.eqb_refl.
     - apply existsb_exists in H.
       inversion H.
       destruct H0.
       apply Nat.eqb_eq in H1. subst i.
       apply H0.
   Qed.

  Lemma nat_in__app_to_front: forall l i m n,
    nat_in i m = nat_in i n 
    -> nat_in i (l ++ m) = nat_in i (l ++ n).
  Proof. 
    intro l.
    induction l as [| x xs]; intros i m n H.
    - simpl. apply H.
    - simpl.
      case (i =? x). auto.
      apply IHxs. apply H.
  Qed.

  (** List/List.v in_app_or *)
  Lemma nat_in_app_or: forall l m x,
    nat_in x (l++m) = (nat_in x l) || (nat_in x m).
  Proof.
    intro l.
    induction l as [| h t]; intros m x.
    simpl. auto.
    simpl. destruct (beq_nat x h).
    simpl. auto. apply IHt.
  Qed.

  
  Lemma nat_in_app_swap: forall l m i,
    nat_in i (l++m) = nat_in i (m++l).
  Proof.
    (*
    intros. 
    destruct (nat_in i (l++m)) eqn:H.
    - apply In__nat_in in H.
      apply in_app_or in H.
      apply or_comm in H.
      apply in_or_app in H.
      apply In__nat_in in H.
      symmetry.
      apply H.
    - 
      *)
    intro l.
    induction l as [| x xs]; intros m i.
    - simpl. rewrite app_nil_r. auto.
    - rewrite <- app_comm_cons.
      simpl.
      remember (beq_nat i x) as r.
      destruct r.
      + apply beq_nat_eq in Heqr.
        rewrite Heqr.
        rewrite nat_in_app_or.
        simpl. rewrite <- beq_nat_refl with (n:=x).
        destruct (nat_in x m); auto.
      + rewrite IHxs.
        assert (nat_in i (m ++ x :: xs) 
          = nat_in i m || nat_in i (x :: xs)) as A1.
        rewrite nat_in_app_or; auto.
        rewrite A1; clear A1.
        simpl.
        rewrite <- Heqr.
        rewrite <- nat_in_app_or.
        auto.
  Qed.
  
  Lemma P_taut: forall (P: Prop), P -> P. 
  Proof. intros P H. auto. Qed. 

  
  (** * From vMemo

   *)


  (** ** Utilities 

   *)

  Definition nat_list_nil := (nil:(list nat)).

  (** [destX x n] destructs [x], [n] times. It can be used to 
      break up n-tuple apart. 
   *)

  Ltac dest_X x n :=
  idtac; 
    let rec dest_X' n :=
        match n with
          | O => idtac
          | S O => idtac
          | S ?n' => let t_0 := fresh "t_0" in
                     destruct x as [x t_0]
                     ; dest_X' n'
        end in
    dest_X' n.

    (** [match_succ_N_tac Sn n] checks if [Sn] has [n] in the form of 
       [n], [S n], or [S (S ... (S n))]. 
     *)
    
  Ltac match_succ_N_tac Sn n :=
    idtac; 
    let rec match_succ_N_tac' Sn :=
        match Sn with
          | O => fail 1
          | S ?Sn' => first [match_succ_N_tac' Sn'| fail 2]
          | _ => 
            let p := fresh "p" in assert(p:=eq_refl n: Sn = n);
                                  clear p; idtac
        end in
    match_succ_N_tac' Sn.



  (** If the structure S (S ...) is not enough deep, then 
      returns fail, that means go on to the next term in [first] clause.
      returning [idtac] means this is enough deep so get out of the loop when
      used in [repeat match goal with].
   *)

  Ltac succ_enough Sn c :=
    let rec succ_enough' x :=
        match x with
          | (_, O) => idtac 
          | (S ?Sn', S ?c') => first [succ_enough' (Sn', c') | fail 2]
          | _ => fail 1
        end in
    succ_enough' (Sn, S c).

  (** Just renamed from [succ_enough]
   *)
  Ltac succ_ge Sn c :=
    let rec succ_ge' x :=
        match x with
          | (    _ ,     O) => idtac 
          | (S ?Sn', S ?c') => first [succ_ge' (Sn', c') | fail 2]
          | _ => fail 1
        end in
    succ_ge' (Sn, c).

  (*
  Example succ_ge_test1: forall n:nat, n = n.
  Proof.
    intro n.
    first [succ_ge (S n) 0| pose "t"].
    first [succ_ge n 0| pose "t"].
    first [succ_ge (S n) (S 0)| pose "t"].
    first [succ_ge (S (S n)) (S 0)| pose "t"].
    first [succ_ge (S n) (S (S 0))| pose "f"].
    reflexivity.
  Qed.
  *)
  
  Ltac succ_lt Sn c :=
      idtac "succ_lt"
    ; let rec succ_lt' x :=
          idtac "x =" x
          ; match x with
              | (  _ ,    O ) => 
                idtac "1"
                ; fail 1
              | (S ?Sn', S ?c') => 
                idtac "2"
                ; first [succ_lt' (Sn', c')| fail 2]
              | _ => 
                idtac "3"
            end in
      succ_lt' (Sn, c).

  (*
  Example succ_lt_test1: forall n:nat, n = n.
  Proof.
    intro n.

    first [succ_lt (S n) 0| pose "f"].
    first [succ_lt (S n) (S 0)| pose "f"].
    first [succ_lt n 0| pose "f"].
    first [succ_lt n (S n)| pose "t"].
    first [succ_lt n (S 0)| pose "t"].
    first [succ_lt (S n) (S (S 0))| pose "t"].
    reflexivity.
  Qed.
  *)
  
  Ltac succ_le Sn c := succ_lt Sn (S c).

  (*
  Example succ_le_test1: forall n:nat, n = n.
  Proof.
    intro n.
    first [succ_le (S n) 0| pose "f"].
    first [succ_le n 0| pose "t"].
    first [succ_le n (S 0)| pose "t"].
    first [succ_le (S n) (S (S 0))| pose "t"].
    reflexivity.
  Qed.
  *)

  Ltac succ_eq Sn c := succ_le Sn c; succ_ge Sn c.

  (*
  Example succ_eq_test1: forall n:nat, n = n.
  Proof.
    intro n.
    first [succ_eq (S n) 0| pose "f"].
    first [succ_eq n 0| pose "t"].
    first [succ_eq (S n) (S 0)| pose "t"].
    first [succ_eq (S n) (S (S 0))| pose "f"].
    first [succ_eq (S (S (S (S n)))) (S (S (S (S 0))))| pose "t"].
    first [succ_eq (S (S (S (S n)))) (S (S (S 0)))| pose "f"].
    reflexivity.
  Qed.
  *)



  (** duplicate a hypothesis
   *)

  Ltac dupH H H':=
    idtac
    ; match type of H with
        | ?X => assert (H':X) by apply H 
      end. 


  (** Next ltac [eqConj_tac] takes a hypothesis [H] in a form of 
      [H: T1 /\ T2 /\ ... /\ True] and a tactic [tac] and 
      apply [tac] to each of the terms except for the last [True].

      For example if the tactic is 
<<
      Ltac rewrite_tac X := idtac; rewrite X. 
>>
      and the hypothesis is 
<<
      [H: x1 = x2 /\ x2 = x3 /\ x3 = x4 /\ ... /\ True] and 
>>      
      Then [eqConj_tac H rewrite_tac.] will apply rewrite to each 
      equality of [H]. 

      Note: 
       - Directly using rewrite, instead of rewrite_tac, does 
         not work. 
       - Since [eqConj_tac] clears each term after applying [tac],
         [tac] itself should not clear the hypothesis.
   *)

  Ltac eqConj_tac H tac :=
    let rec eqConj_tac' H := 
        match type of H with 
          | ?T1 /\ ?T2 => 
            let CH := fresh "CH_0" in 
            let CT := fresh "CT_0" in 
            destruct H as [CH CT]
                          ; tac CH
                          ; clear CH
                          ; eqConj_tac' CT
          | _ => clear H
        end
    in let H_dup := fresh "H_dup" in
       dupH H H_dup 
       ; eqConj_tac' H_dup.

  Ltac rewrite_tac X := idtac; rewrite X.
  Ltac rewrite_all_tac X := idtac; rewrite X in *.

  Example EqConj_tac_test2: 
    forall {A: Type} (x1 x2 x3 x4 :A),
      x1 = x2 /\ True ->
      x1 = x2.
  Proof.
    intros.
    eqConj_tac H rewrite_tac.
    intuition.
  Qed.

  Example EqConj_tac_test3: 
    forall {A: Type} (x1 x2 x3 x4 :A),
      x1 = x2 /\ x2 = x3 /\ x3 = x4 /\ True ->
      x1 = x4.
  Proof.
    intros.
    eqConj_tac H rewrite_tac.
    intuition.
  Qed.
 

  
  (** When we have an equation of tuples as a hypothesis, 
      such as [H: (x1,x2) = (y1,y2)], 
      an inversion on that hypothesis equates the corresponding 
      tuple members. The next tactic [invertTupleRewriteRev] also does that 
      in a controled manner, in particular, trying to replace the 
      the members of right-side tuple with the corresponding 
      members in left-side tuple. 
      
      The maximum size of tuple is now limited to six. 

   *)

  Ltac invertTupleRewriteRev H :=
    idtac "invertTupleRewriteRev"
    ; match type of H with

        | (?X1, ?X2, ?X3, ?X4, ?X5, ?X6) = (?Y1, ?Y2, ?Y3, ?Y4, ?Y5, ?Y6) => 
          let Tm1 := fresh "Tm1" in
          let Tm2 := fresh "Tm2" in
          let Tm3 := fresh "Tm3" in
          let Tm4 := fresh "Tm4" in
          let Tm5 := fresh "Tm5" in
          let Tm6 := fresh "Tm6" in
          assert (X1 = Y1 /\ X2 = Y2 /\ X3 = Y3 /\ X4 = Y4 /\ X5 = Y5 /\ X6 = Y6) 
            as [Tm1 [Tm2 [Tm3 [Tm4 [Tm5 Tm6]]]]] by 
                (inversion H
                 ; try subst
                 ; intuition
                )
          ; try rewrite <- Tm1
          ; try rewrite <- Tm2
          ; try rewrite <- Tm3
          ; try rewrite <- Tm4
          ; try rewrite <- Tm5
          ; try rewrite <- Tm6

        | (?X1, ?X2, ?X3, ?X4, ?X5) = (?Y1, ?Y2, ?Y3, ?Y4, ?Y5) => 
          let Tm1 := fresh "Tm1" in
          let Tm2 := fresh "Tm2" in
          let Tm3 := fresh "Tm3" in
          let Tm4 := fresh "Tm4" in
          let Tm5 := fresh "Tm5" in
          assert (X1 = Y1 /\ X2 = Y2 /\ X3 = Y3 /\ X4 = Y4 /\ X5 = Y5) 
            as [Tm1 [Tm2 [Tm3 [Tm4 Tm5]]]] by 
                (inversion H
                 ; try subst
                 ; intuition
                )
          ; try rewrite <- Tm1
          ; try rewrite <- Tm2
          ; try rewrite <- Tm3
          ; try rewrite <- Tm4
          ; try rewrite <- Tm5

        | (?X1, ?X2, ?X3, ?X4) = (?Y1, ?Y2, ?Y3, ?Y4) => 
          let Tm1 := fresh "Tm1" in
          let Tm2 := fresh "Tm2" in
          let Tm3 := fresh "Tm3" in
          let Tm4 := fresh "Tm4" in
          assert (X1 = Y1 /\ X2 = Y2 /\ X3 = Y3 /\ X4 = Y4) 
            as [Tm1 [Tm2 [Tm3 Tm4]]] by 
                (inversion H
                 ; try subst
                 ; intuition
                )
          ; try rewrite <- Tm1
          ; try rewrite <- Tm2
          ; try rewrite <- Tm3
          ; try rewrite <- Tm4
        | (?X1, ?X2, ?X3) = (?Y1, ?Y2, ?Y3) => 
          let Tm1 := fresh "Tm1" in
          let Tm2 := fresh "Tm2" in
          let Tm3 := fresh "Tm3" in
          assert (X1 = Y1 /\ X2 = Y2 /\ X3 = Y3) 
            as [Tm1 [Tm2 Tm3]] by 
                (inversion H
                 ; try subst
                 ; intuition
                )
          ; try rewrite <- Tm1
          ; try rewrite <- Tm2
          ; try rewrite <- Tm3
                  
        | (?X1, ?X2) = (?Y1, ?Y2) => 
          let Tm1 := fresh "Tm1" in
          let Tm2 := fresh "Tm2" in
          assert (X1 = Y1 /\ X2 = Y2) 
            as [Tm1 Tm2] by
                (inversion H
                 ; try subst
                 ; intuition
                )
          ; try rewrite <- Tm1
          ; try rewrite <- Tm2
                                                         
        | ?X = ?Y => idtac (* do nothign *)
          ; try rewrite <- H                       

        | _ => idtac "invertTuple: error"
    end.



  Example invertTupleRewriteRev_test6: 
    forall {A: Type} (x1 x2 x3 x4 x5 x6 y1 y2 y3 y4 y5 y6:A),
      (x1,x2,x3,x4,x5,x6) = (y1,y2,y3,y4,y5,y6) ->
      x1 = y1 /\ x2 = y2 /\ x3 = y3 /\ x4 = y4
      /\ x5 = y5 /\ x6 = y6.
  Proof.
    intros.
    invertTupleRewriteRev H.
    intuition.
  Qed.

  Example invertTupleRewriteRev_test5: 
    forall {A: Type} (x1 x2 x3 x4 x5 y1 y2 y3 y4 y5:A),
      (x1,x2,x3,x4,x5) = (y1,y2,y3,y4,y5) ->
      x1 = y1 /\ x2 = y2 /\ x3 = y3 /\ x4 = y4
      /\ x5 = y5.
  Proof.
    intros.
    invertTupleRewriteRev H.
    intuition.
  Qed.

  Example invertTupleRewriteRev_test4: 
    forall {A: Type} (x1 x2 x3 x4 y1 y2 y3 y4:A),
      (x1,x2,x3,x4) = (y1,y2,y3,y4) ->
      x1 = y1 /\ x2 = y2 /\ x3 = y3 /\ x4 = y4.
  Proof.
    intros.
    invertTupleRewriteRev H.
    intuition.
  Qed.

  Example invertTupleRewriteRev_test3: 
    forall {A: Type} (x1 x2 x3 y1 y2 y3 :A),
      (x1,x2,x3) = (y1,y2,y3) ->
      x1 = y1 /\ x2 = y2 /\ x3 = y3.
  Proof.
    intros.
    invertTupleRewriteRev H.
    intuition.
  Qed.

  Example invertTupleRewriteRev_test2: 
    forall {A: Type} (x1 x2 y1 y2 :A),
      (x1,x2) = (y1,y2) ->
      x1 = y1 /\ x2 = y2.
  Proof.
    intros.
    invertTupleRewriteRev H.
    intuition.
  Qed.

  Example invertTupleRewriteRev_test1: 
    forall {A: Type} (x1 y1 :A),
      x1 = y1 ->
      x1 = y1.
  Proof.
    intros.
    invertTupleRewriteRev H.
    intuition.
  Qed.

  (** The next tactic [invertTuple] is similar to 
      [invertTupleRewriteRev] except it just put the equalities into 
      the context. 
   *)

  Ltac invertTuple H :=
    idtac "invertTuple"
    ; match type of H with

        | (?X1, ?X2, ?X3, ?X4, ?X5, ?X6) = (?Y1, ?Y2, ?Y3, ?Y4, ?Y5, ?Y6) => 
          let Tm1 := fresh "Tm1" in
          let Tm2 := fresh "Tm2" in
          let Tm3 := fresh "Tm3" in
          let Tm4 := fresh "Tm4" in
          let Tm5 := fresh "Tm5" in
          let Tm6 := fresh "Tm6" in
          assert (X1 = Y1 /\ X2 = Y2 /\ X3 = Y3 /\ X4 = Y4 /\ X5 = Y5 /\ X6 = Y6) 
            as [Tm1 [Tm2 [Tm3 [Tm4 [Tm5 Tm6]]]]] by 
                (inversion H
                 ; try subst
                 ; intuition
                )
        | (?X1, ?X2, ?X3, ?X4, ?X5) = (?Y1, ?Y2, ?Y3, ?Y4, ?Y5) => 
          let Tm1 := fresh "Tm1" in
          let Tm2 := fresh "Tm2" in
          let Tm3 := fresh "Tm3" in
          let Tm4 := fresh "Tm4" in
          let Tm5 := fresh "Tm5" in
          assert (X1 = Y1 /\ X2 = Y2 /\ X3 = Y3 /\ X4 = Y4 /\ X5 = Y5) 
            as [Tm1 [Tm2 [Tm3 [Tm4 Tm5]]]] by 
                (inversion H
                 ; try subst
                 ; intuition
                )

        | (?X1, ?X2, ?X3, ?X4) = (?Y1, ?Y2, ?Y3, ?Y4) => 
          let Tm1 := fresh "Tm1" in
          let Tm2 := fresh "Tm2" in
          let Tm3 := fresh "Tm3" in
          let Tm4 := fresh "Tm4" in
          assert (X1 = Y1 /\ X2 = Y2 /\ X3 = Y3 /\ X4 = Y4) 
            as [Tm1 [Tm2 [Tm3 Tm4]]] by 
                (inversion H
                 ; try subst
                 ; intuition
                )

        | (?X1, ?X2, ?X3) = (?Y1, ?Y2, ?Y3) => 
          let Tm1 := fresh "Tm1" in
          let Tm2 := fresh "Tm2" in
          let Tm3 := fresh "Tm3" in
          assert (X1 = Y1 /\ X2 = Y2 /\ X3 = Y3) 
            as [Tm1 [Tm2 Tm3]] by 
                (inversion H
                 ; try subst
                 ; intuition
                )
                  
        | (?X1, ?X2) = (?Y1, ?Y2) => 
          let Tm1 := fresh "Tm1" in
          let Tm2 := fresh "Tm2" in
          assert (X1 = Y1 /\ X2 = Y2) 
            as [Tm1 Tm2] by 
                (inversion H
                 ; try subst
                 ; intuition
                )
                                                         
        | ?X = ?Y => idtac (* do nothign *)

        | _ => idtac "invertTuple: error"
    end.

  Example invertTuple_test6: 
    forall {A: Type} (x1 x2 x3 x4 x5 x6 y1 y2 y3 y4 y5 y6:A),
      (x1,x2,x3,x4,x5,x6) = (y1,y2,y3,y4,y5,y6) ->
      x1 = y1 /\ x2 = y2 /\ x3 = y3 /\ x4 = y4
      /\ x5 = y5 /\ x6 = y6.
  Proof.
    intros.
    invertTuple H.
    intuition.
  Qed.

  Example invertTuple_test5: 
    forall {A: Type} (x1 x2 x3 x4 x5 y1 y2 y3 y4 y5:A),
      (x1,x2,x3,x4,x5) = (y1,y2,y3,y4,y5) ->
      x1 = y1 /\ x2 = y2 /\ x3 = y3 /\ x4 = y4
      /\ x5 = y5.
  Proof.
    intros.
    invertTuple H.
    intuition.
  Qed.


  Example invertTuple_test3: 
    forall {A: Type} (x1 x2 x3 y1 y2 y3 :A),
      (x1,x2,x3) = (y1,y2,y3) ->
      x1 = y1 /\ x2 = y2 /\ x3 = y3.
  Proof.
    intros.
    invertTuple H.
    intuition.
  Qed.

  Example invertTuple_test2: 
    forall {A: Type} (x1 x2 y1 y2 :A),
      (x1,x2) = (y1,y2) ->
      x1 = y1 /\ x2 = y2.
  Proof.
    intros.
    invertTuple H.
    intuition.
  Qed.

  Example invertTuple_test1: 
    forall {A: Type} (x1 y1 :A),
      x1 = y1 ->
      x1 = y1.
  Proof.
    intros.
    invertTuple H.
    intuition.
  Qed.


  (** [destN] stands for [destruct n]. If the parameter [n]
      is a constant, then this recursion reaches [O] and execute 
      [idtac], that means get out of the first 

      e.g.
      S (S (S n)) ==> S (S n) ==> S n ==> n ==> destruct n

   *)

  Ltac dest_N n :=
    let rec dest_N' n :=
        match n with
          | O => fail 1
          | S ?n' => first [dest_N' n'| fail 2]
          | _ => destruct n; idtac
        end in
    dest_N' n.


  Unset Ltac Debug.

  Ltac clear_context_tac :=
    idtac;
    repeat match goal with 
             | [H: ?X|- _ ] => idtac H; clear H
           end.
  
  Ltac revert_all_tac :=
    idtac; 
    repeat match goal with 
             | [H: ?X |- _] => revert H
           end. 

  Ltac revert_all_except_tac 
       T :=
    idtac; 
    repeat match goal with 
             | [H: ?X |- _] => 
               match type of T with 
                 | X => idtac
                 | _ => revert H
               end
           end. 

  

  Ltac clear_context_except_tac 
       T :=
    idtac;
    repeat match goal with 
             | [H: ?X|- _ ] => 
               match type of T with
                 | X => idtac
                 | _ => clear H
               end
           end.

  Ltac clear_context_except2_tac 
       T1 T2 :=
    idtac;
    repeat match goal with 
             | [H: ?X|- _ ] => 
               match type of T1 with
                 | X => idtac
                 | _ => 
                   match type of T2 with
                     | X => idtac 
                     | _ => clear H
                   end
               end
           end.


  Ltac introN n :=
    idtac; 
    match n with
      | O => idtac
      | S ?n' => intro; introN n'
    end.





  Ltac tac_le := fun a b => 
                   assert (leb a b = true); unfold leb;
                   match goal with 
                     | [|- true = true ] => idtac 
                     | [|- false = true ] => fail 1
                     | [H: leb a b = true |- _] => idtac
                     | _ => fail 1
                   end.

  (*
  (** [succ_X_auto_tac x] is [succ_X_tac x n] that detects [n] from the form [x > n] in 
     the context. 
   *)

  Ltac succ_X_auto_tac x :=
      repeat match goal with
             | [NS: ?j > ?basecase_const |- _] => 
                 idtac "succ_X_tac: 1st branch, j =" j;
                 (tac_le j basecase_const; 
                 absurd (j > basecase_const); auto with arith;
                 idtac "after inversion")
              | [NS: ?Sn > ?basecase_const |- _] => 
                 idtac "succ_X_tac: 2nd branch, Sn =" Sn;
                (match_succ_N_tac Sn x;
                 first [succ_enough Sn basecase_const | dest_N Sn ]; 
                 idtac "Sn was not enoguh, so destructed again the boddom n of Sn")

           end.

  Lemma n_gt_n__False: forall n,
    n > n -> False.
  Proof.
    intros n H.
    omega.
  Qed.
  
  Example succ_X_auto_tac_test: 
    forall n, n > 1 -> n > 0. 
  intros. succ_X_auto_tac n;
            inversion H; auto.
  auto with arith.
  Qed.


  Ltac succ_auto_all_rev_tac:= 
    idtac; 
    repeat match goal with 
      | [H: ?v > ?c |- _] =>
        assert (c < v) by auto with arith; 
          succ_X_auto_tac v;
          clear H
    end.

  Ltac flip_lt_tac:= 
    idtac; 
    repeat match goal with 
             | [H: ?v < ?c |- _] =>
               assert (c > v) by auto with arith; 
                 clear H
           end.

  Ltac succ_auto_all_tac:=
    idtac; 
    succ_auto_all_rev_tac; flip_lt_tac.


  Example succ_auto_all_tac_test1:
    forall n1 n2, n1 > 1 -> n2 > 2 -> (n1 + n2) > 3.
    intros.
    succ_auto_all_tac.
    omega.
  Qed.
  *)

  (** Next function [disjnF] is to make disjunctions 
<<
   n = 0 \/ n = 1 \/ n = 2 \/ ... \/ n = (bn - 1) \/ n > (bn - 1)
>>
   *)

  Definition disjnF (bn n:nat) :=
    match bn with 
      | O => True
      | S bn' => 
        let fix f c :=
            match c with 
              | O => n = O
              | S c' => (f c' \/ n = c) 
            end
        in (f bn' \/ n > bn')
    end.


  (** This tactic [disj_N_tac] force case analysis over 
     [bn] base cases and one inductive case of [n].       
   *)

  Ltac disj_N_tac bn n:=
    let N := fresh "N" in
    assert (N: disjnF bn n) by (unfold disjnF; omega); unfold disjnF in N;
    repeat match goal with 
             | [N : _ \/ _ |- _] => destruct N as [N|N]
           end.


  Ltac succ_N_tac basecase_const :=
      repeat match goal with
             | [NS: ?j > basecase_const |- _] => 
                (tac_le j basecase_const; 
                 absurd (j > basecase_const); auto with arith; 
                 idtac "after inversion")
              | [NS: ?Sn > basecase_const |- _] => 
                idtac; 
                (first [succ_enough Sn basecase_const | dest_N Sn ]; 
                 idtac "Sn was not enoguh, so destructed again the boddom n of Sn")

           end.


  Ltac pred_nat n :=
    match n with 
      | O => O 
      | S ?n' => n'
    end.


  (* [] *)


  (*
  (** [succ_X_tac x n] destructs [x] in the context [n] + 1 times assuming that
      [S x <= n] is absurd. This is a modification of [succ_N_tac] so that we can
      specify the variable to work on. This is needed when we have two or
      more variables that has the form [x > c] for some constant [basecase_const]
      [c].  
   *)

  Ltac succ_X_tac x basecase_const :=
      repeat match goal with
             | [NS: ?j > basecase_const |- _] => 
                 idtac "succ_X_tac: 1st branch, j =" j;
                 (tac_le j basecase_const; 
                 absurd (j > basecase_const); auto with arith;
                 idtac "after inversion")
              | [NS: ?Sn > basecase_const |- _] => 
                 idtac "succ_X_tac: 2nd branch, Sn =" Sn;
                (match_succ_N_tac Sn x;
                 first [succ_enough Sn basecase_const | dest_N Sn ]; 
                 idtac "Sn was not enoguh, so destructed again the boddom n of Sn")

           end.


  Ltac succ_auto_tac :=
      repeat match goal with
             | [NS: ?j > ?basecase_const |- _] => 
                 idtac "succ_auto_tac: 1st branch, j =" j;
                 (tac_le j basecase_const; 
                 absurd (j > basecase_const); auto with arith;
                 idtac "after inversion")
              | [NS: ?Sn > ?basecase_const |- _] => 
                 idtac "succ_auto_tac: 2nd branch, Sn =" Sn;
                (
                 first [succ_enough Sn basecase_const | dest_N Sn ]; 
                 idtac "Sn was not enoguh, so destructed again the boddom n of Sn")
           end.
  Unset Ltac Debug.


  Example succ_auto_tac_test: 
    forall n, n > 1 -> n > 0. 
    intros. succ_auto_tac. omega.
  Qed.

  *)
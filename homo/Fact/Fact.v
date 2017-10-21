(**
<<
  [1] Pottier, Francois. loop (Dec 11, 2014), fpottier. 
         https://github.com/fpottier/loop
 
>>
*)



  Require Import homo.MyLib.
  Require Import homo.FoldLib.
  Require Import Recdef.
  
  Definition g (s: nat * nat) : option (nat * nat) := 
    let (n, m) := s in
    match m with 
      | O => None
      | S m' => Some (n-1, m')
    end.

  Definition snd_lt (s' s: nat * nat) := (snd s') < (snd s).

  Lemma g_lt: 
    forall s s', 
      g s = Some s' -> snd_lt s' s.
  Proof. 
    intros.
    unfold g in H.
    destruct s as [n m].
    destruct m as [| m].
    - inversion H.
    - inversion H.
      unfold snd_lt.
      auto.
  Defined. 

  Require Import Coq.Arith.Wf_nat. 
  Require Import Coq.Wellfounded.Inverse_Image.
  
  Lemma snd_lt_wf: well_founded snd_lt.
  Proof.
    unfold snd_lt.
    eapply wf_inverse_image.
    eapply lt_wf.
  Defined.

  Definition cr (s: nat * nat) (seed: nat) :=
    let (n, m) := s in (S n) * seed. 

  Infix "(+)" := cr (at level 80, right associativity).  
  
  Function fact_sep 
             (seed: nat)
             (s: nat * nat) {wf snd_lt s} : nat:=
      match (g s) with
        | None     => seed 
        | Some s' => s' (+) (fact_sep seed s')
      end. 
  Proof.
    intros. 
    apply g_lt.
    exact teq.
    exact snd_lt_wf.
  Defined. 

  Fixpoint fact (n:nat) :=
    match n with
    | O => 1
    | S n' => n * fact n'
    end.

  Theorem fact_sep__fact: forall n,
      fact_sep 1 (n,n) = fact n.
  Proof. 
    intro n. 
    induction n as [| n]; rewrite fact_sep_equation; auto.
    simpl.
    rewrite Nat.sub_0_r.
    rewrite IHn.
    reflexivity.
  Qed.
  

  (** *** [fact_sep_prog] 
      
      To run a test for [fact_sep]. 
   *)
  Fixpoint fact_sep_prog (seed n m: nat) := 
    match m with
    | O => seed
    | S m' => n * (fact_sep_prog seed (n-1) m')
    end.

  Eval compute in (fact_sep_prog 1 5 5).
  Eval compute in (fact 5).
    
  Theorem fact_sep__fact_sep_prog:
    forall m n seed,
      n >= m -> 
      fact_sep seed (n,m) = fact_sep_prog seed n m.
  Proof. 
    intro.
    induction m; intros;
      rewrite fact_sep_equation;
      unfold g; unfold cr. 
    
    unfold fact_sep_prog. reflexivity.
    destruct n as [| n]. inversion H.
    assert(A1: n >= m) by auto with arith. clear H.
    rewrite IHm.
    2: omega.
    simpl.
    rewrite <- minus_n_O. 
    reflexivity.
  Qed. 


  (** ** Splitting 

   *)
  
  Definition split_nm (n m: nat) :=
    let m1 := div2 m in
    let m2 := m - m1 in
    let n1 := n  in
    let n2 := n1 - m1 in
    (n1, m1, n2, m2).

  
  Definition SplitPred (t1 t2: nat * nat) :=
    let (n1,m1) := t1 in
    let (n2,m2) := t2 in
    n2 = n1 - m1.

  Lemma Associative: 
    forall a b c,
      cr a (b * c) = cr a b * c.
  Proof.
    intros [n m] b c.
    unfold cr.
    auto with arith.
  Qed.

  Lemma Unit:
    forall (seed : nat), 
      seed = 1 * seed.
  Proof. 
    auto with arith.
  Qed. 

  Definition scat (s1 s2: nat * nat) := (fst s1, (snd s1) + (snd s2)).

  Lemma Base_Omitted: 
    forall s1 s2, 
      SplitPred s1 s2 -> 
      g s1 = None ->
      scat s1 s2 = s2.
  Proof.
    unfold SplitPred.
    intros [n1 m1] [n2 m2] Sp * Gs1.
    unfold scat in *.
    simpl in *.
    destruct m1.
    - rewrite <- minus_n_O in Sp.
      rewrite plus_0_l.
      subst n2.
      reflexivity.
    - inversion Gs1.
  Qed.

  Lemma Recursive_Retention_R:
    forall s1 s2 s : nat * nat,
      SplitPred s1 s2 ->
      g s1 = Some s ->
      g (scat s1 s2) = Some (scat s s2).
  Proof. 
    intros * H Sp.
    clear H.
    unfold SplitPred in Sp.
    destruct s1 as [n1 m1].
    destruct s2 as [n2 m2].
    destruct s as [n1' m1'].
    unfold scat.
    simpl.
    unfold g in Sp.
    induction m1 as [| m1].
    inversion Sp.
    inversion Sp.
    subst n1' m1'.
    simpl.
    reflexivity.
  Qed. 

  Lemma Recursive_Retension_L:
    forall s1 s2: nat * nat,
      SplitPred s1 s2 ->
    forall s : nat * nat,
      g s1 = Some s -> SplitPred s s2. 
  Proof. 
    intros [n1 m1] [n2 m2] Sp [n3 m3] Gs1.
    unfold SplitPred; unfold scat in *.
    simpl in *.
    destruct m1; inversion Gs1.
    injection Gs1. intros M1 N3.
    subst m3.
    omega. 
  Qed.
  
  Lemma Head_Access:
   forall (s1 s2 : nat * nat),
     SplitPred s1 s2 ->
     forall (b : nat),
     cr (scat s1 s2) b = cr s1 b.
  Proof.
    intros [n1 m1] [n2 m2] * Sp.
    clear Sp.
    unfold scat in *.
    simpl in *.
    reflexivity.
  Qed.

  
  Lemma fact_sep_homomorphism: 
    forall t1 t2, 
      SplitPred t1 t2 -> 
      fact_sep 1 (scat t1 t2) = 
      (fact_sep 1 t1) * (fact_sep 1 t2).
  Proof.
    Unset Ltac Debug.
    linU_homomorphism_tac
      fact_sep_equation
      Base_Omitted
      Recursive_Retention_R
      Head_Access
      Recursive_Retension_L
      Unit
      Associative
    .     
  Qed. 

  Lemma Head_Access':
   forall (s1 s2 : nat * nat),
     SplitPred s1 s2 ->
     forall (b : nat),
       cr (scat s1 s2) b = cr s1 b.
  Proof.
    intros [n1 m1] [n2 m2] * Sp. 
    unfold scat in *.
    simpl in *.
    reflexivity.
  Qed.



  Function fact_homo (t: nat * nat) {wf snd_lt t} :=
    match t with
      | (n, m) => 
    match m with
    | O => 1
    | S O => n 
    | S m' => match split_nm n m with
              | (n1,m1,n2,m2) =>
                let v1 := (fact_homo (n1, m1)) in
                let v2 := (fact_homo (n2, m2)) in
                v1 * v2
              end
    end
    end.

  Proof. 
    - intros.
      unfold split_nm in teq2.
      injection teq2; intros.
      unfold snd_lt. simpl. subst.
      case (Nat.div2 n0) eqn: H; auto. 
      omega. 
    - intros.
      unfold split_nm in teq2.
      injection teq2; intros. 
      unfold snd_lt. simpl. 
      subst.
      destruct n0; auto with arith.
    - apply snd_lt_wf.
  Defined.

  Definition split_nat (n:nat) := 
    let n1 := div2 n in 
    let n2 := n - n1 in
    (n1, n2).

  Eval compute in (split_nat 10).
  Eval compute in (split_nat 0).


  Function fact_homo_prog (n m: nat) {measure (fun n: nat => n) m } :=
    match m with
      | O => 1
      | S O => n
      | S m' =>
          let (m1, m2) := split_nat m in
          let v1 := (fact_homo_prog n m1) in
          let v2 := (fact_homo_prog (n-m1) m2) in
          v1 * v2
    end.
  Proof. 
    - intros. 
      unfold split_nat in teq1.
      inversion teq1.
      case (Nat.div2 n0) eqn: DivN0; omega. 
    - intros.
      unfold split_nat in teq1.
      inversion teq1.
      destruct n0; auto with arith.
  Defined.

  
  Eval compute in (split_nm 3 3).
  Eval compute in (fact_homo_prog 4 2).

  
  
  Theorem fact_sep__fact_homo:
    forall n m,
      n >= m -> 
      fact_sep 1 (n, m) = fact_homo (n,m).
  Proof.
    
    intros n m.
    name_term t (n, m) T. rewrite <- T.
    generalize dependent T.
    generalize dependent m.
    generalize dependent n.
    
    functional induction (fact_homo t); intros * T VT;
      injection T; clear T; intros; subst m n0.    
    - rewrite fact_sep_equation; auto.
    - destruct n as [| n]. inversion VT.
      rewrite fact_sep_equation; simpl.
      rewrite fact_sep_equation; simpl.
      rewrite Nat.sub_0_r.
      auto with arith.
    - destruct n as [| n]. inversion VT.
      assert(VT': n >= m') by auto with arith; clear VT; rename VT' into VT.
      unfold split_nm in e1;
        apply invertTupleRewriteRev_test4 in e1 as [N1 [M1 [N2 M2]]].
      assert (A1: n2 >= m2) by omega. 
      assert (A2: n1 >= m1). 
      {
        subst.
        apply le_trans with (m:=S m').
        apply le_div2.
        auto with arith.
      }
      erewrite <- IHn; auto; clear IHn.
      erewrite <- IHn0; auto; clear IHn0.

      assert (Sp: SplitPred (n1,m1) (n2,m2)) by (unfold SplitPred; omega).
      apply fact_sep_homomorphism in Sp.

      rewrite <- Sp.
      unfold scat. simpl.
      subst n1.
      assert (A46: S m' = m1 + m2). {
        assert (m1 <= m').
        {
          subst; simpl.
          destruct m'; trivial.
          apply le_n_S.
          apply le_div2.
        }
        omega. 
      } 
    rewrite A46.
    reflexivity.

  Restart.
    intros n m.
    name_term t (n, m) T. rewrite <- T.
    generalize dependent T.
    generalize dependent m.
    generalize dependent n.
    
    functional induction (fact_homo t); intros * T VT;
      injection T; clear T; intros; subst m n0.    
    - rewrite fact_sep_equation; auto.
    - destruct n as [| n]. inversion VT.
      rewrite fact_sep_equation; simpl.
      rewrite fact_sep_equation; simpl.
      rewrite Nat.sub_0_r.
      auto with arith.
    - destruct n as [| n]. inversion VT.
      assert(VT': n >= m') by auto with arith; clear VT; rename VT' into VT.
      unfold split_nm in e1;
        apply invertTupleRewriteRev_test4 in e1 as [N1 [M1 [N2 M2]]].
      assert (A1: n2 >= m2) by omega. 
      assert (A2: n1 >= m1). 
      {
        subst.
        apply le_trans with (m:=S m').
        apply le_div2.
        auto with arith.
      }
      erewrite <- IHn; auto; clear IHn.
      erewrite <- IHn0; auto; clear IHn0.

      assert (Sp: SplitPred (n1,m1) (n2,m2)) by (unfold SplitPred; omega).
      apply fact_sep_homomorphism in Sp.

      rewrite <- Sp.
      unfold scat. simpl.
      subst n1.
      assert (A46: S m' = m1 + m2). {
        assert (m1 <= m').
        {
          subst; simpl.
          destruct m'; trivial.
          apply le_n_S.
          apply le_div2.
        }
        omega. 
      } 
    rewrite A46.
    reflexivity.
  
  
  
  Qed.


  
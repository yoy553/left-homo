(**
<<
   This is a library of Ltac that shows equivalence between two implementations: 

>>

 *)


  Require Export List.

  Ltac specializeWithBlank_tac Gen n_vars Hyp :=
    match n_vars with
      | O =>                                                   specialize (Gen Hyp) 
      | S O =>                                                 specialize (Gen _ Hyp) 
      | S (S O) =>                                             specialize (Gen _ _ Hyp) 
      | S (S (S O)) =>                                         specialize (Gen _ _ _ Hyp) 
      | S (S (S (S O))) =>                                     specialize (Gen _ _ _ _ Hyp) 
      | S (S (S (S (S O)))) =>                                 specialize (Gen _ _ _ _ _ Hyp) 
      | S (S (S (S (S (S O))))) =>                             specialize (Gen _ _ _ _ _ _ Hyp) 
      | S (S (S (S (S (S (S O)))))) =>                         specialize (Gen _ _ _ _ _ _ _ Hyp) 
      | S (S (S (S (S (S (S (S O))))))) =>                     specialize (Gen _ _ _ _ _ _ _ _ Hyp) 
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


  
  Ltac f_functional_ind_FI_IH f FI IH :=
    idtac "f_functional_ind_FI_IH: start";
    idtac f; 
    match goal with
    | |- context [f ?X ?Y ?Z] => idtac "f_functional_ind_FI_IH: f X Y Z";
                                 functional induction (f X Y Z) as [* FI| * FI IH]      
    | |- context [f ?X ?Y] => idtac "f_functional_ind_FI_IH: f X Y";
                              functional induction (f X Y) as [* FI| * FI IH]
    | |- context [f ?X] => idtac "f_functional_ind_FI_IH: f X";
                           functional induction (f X) as [* FI| * FI IH]
    | |- context [f] => idtac "f_functional_ind_FI_IH: f";
                        functional induction (f) as [* FI| * FI IH]
    end. 

  Ltac f_equation_r_unfold f f_equation :=
    let XXX := fresh "XXX" in  
    match goal with
    | |- ?X = _ => set (XXX:=X)
    end; 
    match goal with
    | |- _ = f ?X ?Y ?Z => rewrite f_equation                                      
    | |- _ = f ?X ?Y => rewrite f_equation
    | |- _ = f ?X  => rewrite f_equation
    | |- _ = f     => rewrite f_equation

    end;
    unfold XXX; clear XXX.



 
 
  Ltac dupH H H':=
    idtac
    ; match type of H with
        | ?X => assert (H':X) by apply H 
      end. 

  Require Export MyLib. (* name_term *)

  Ltac linU_inclusion_tac
         linU
         linU_equation 
         Base_Omitted
         Recursive_Retention_R
         Head_Access
         SplitPred
         Recursive_Retention_L

      :=
 
  idtac "incl_01"  ; let S1 := fresh "S1" in
                     intros * S1
; idtac "incl_02"  ; let M2' := fresh "M2'" in
                     let m2' := fresh "m2'" in
                     let FI  := fresh "FI" in
                     let IH  := fresh "IH" in
  idtac "incl_08"  ; let base_tac := 
                         (fun FI => erewrite Base_Omitted
                                    ; [auto| (apply S1; auto)
                                       | (try apply FI; auto)] ) in
  idtac "incl_09"  ; let rec_tac :=
                         (fun FI IH X1 X2 => rewrite linU_equation
                          (** FI: g m1 = xxx
                           *)
                          ; let SP' := fresh "SP'" in
                            match type of IH with
                              SplitPred ?m1' _ -> _ => 
                              assert (SP': SplitPred m1' X2)  
                                by
                                  (eapply Recursive_Retention_L; 
                                   [apply S1 | (try apply FI; auto)])
                            end
                          ; let SP := fresh "SP" in
                            dupH SP' SP                                   
                          ; erewrite Recursive_Retention_R
                          ; [ (apply IH in SP'
                               ; rewrite SP'
                               ; trivial)
                            | try apply S1
                            | (try apply FI; auto)]
                          ; eapply Head_Access   (* to rule out the catted-latter from the argument *)
                          ; (apply SP||apply S1) (* consider two cases, original hd or new hd *)
                         ) in
  idtac "incl_03"      ; match goal with
                         | |- context [linU ?seed (?scat ?X1 ?X2) = linU ?Y ?Z] =>
  idtac "incl_04"              ; name_term m2' Y M2'
; idtac "incl_05"              ; rewrite <- M2'
; idtac "incl_10"              ; functional induction (linU m2' Z) as [* FI| * FI IH] 
; idtac "incl_11"              ; [> base_tac FI | rec_tac FI IH X1 X2]
                         end.





    Ltac linU_slideout_tac
         linU
         linU_equation 
         binop
         z_binop
         cr_binop_assoc
      :=
                     let FI := fresh "FI" in
                     let IH := fresh "IH" in
                     let M' := fresh "M'" in
                     let e_m := fresh "e_m" in
                     let base_tac := 
                         (fun FI =>
                            rewrite linU_equation
                            ; (try rewrite FI; auto); apply z_binop)
                     in
                     let rec_tac :=
                         (fun FI IH SEED M BINOP X =>
                            match goal with
                            | |- context [BINOP ?Y SEED] => 
                              name_term e_m Y M' 
                              ; rewrite <- M'
                              ; rewrite linU_equation in M'
                              ; try rewrite FI in M'
                              ; rewrite M'
                              ; rewrite IH
                              ; apply cr_binop_assoc
                            end)
                     in
                     intros
; idtac "slide_01" ; match goal with
                     | |- context [linU ?SEED ?M = ?BINOP ?X ?SEED] =>
                       functional induction (linU SEED M) as [* FI | * FI IH]
                       ; [> base_tac FI | rec_tac FI IH SEED M BINOP X]
                     end.


                     
  Unset Ltac Debug.

    
    Ltac linU_homomorphism_tac
         linU_equation 

         (** conditions for inclusiotn lemma *)
         Base_Omitted
         Recursive_Retention_R
         Head_Access
         Recursive_Retention_L

         (** conditions for slide-out lemma *)
         binop_e
         cr_binop_assoc

    :=
                     let s1 := fresh "s1" in
                     let s2 := fresh "s2" in
                     let Sp := fresh "Sp" in
                     let IncLem := fresh "IncLem" in
                     intros s1 s2 
                     ; match goal with
                       | |- ?SPLIT_PRED s1 s2 ->
                         ?LinU ?E (?SCAT s1 s2) = ?BINOP (?LinU ?E s1) (?LinU ?E s2)
                            => 
                            idtac ""
                     ; intro Sp
                     ; assert (IncLem: LinU E (SCAT s1 s2) = LinU (LinU E s2) s1)
                     by 
                              (revert Sp;
                               revert s1 s2;
                               
                               linU_inclusion_tac
                                 LinU
                                 linU_equation 
                                 Base_Omitted
                                 Recursive_Retention_R
                                 Head_Access
                                 SPLIT_PRED
                                 Recursive_Retention_L)
                     ; rewrite IncLem
                     ; clear IncLem
                     ; clear Sp
                     ; let seed := fresh "seed" in
                       let Seed := fresh "Seed" in
                       name_term seed (LinU E s2) Seed
                       ; rewrite <- Seed
                       ; generalize seed
                       ; clear Seed seed s2
                       ; revert s1
                       ; linU_slideout_tac
                           LinU
                           linU_equation 
                           BINOP
                           binop_e
                           cr_binop_assoc
                       end
    .




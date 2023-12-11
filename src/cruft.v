Lemma deadbranch : my_EQ iprog1 iprog2.
Proof. 
     unfold my_EQ.
    unfold iprog1.
    (* unfold iprog1 *)
    setoid_rewrite den_iprog1_point.
    (* process bb1 *)
    setoid_rewrite den_bb1.
    setoid_rewrite bind_bind.
    setoid_rewrite bind_ret_.
    setoid_rewrite interp_asm_SetReg.
    setoid_rewrite bind_bind.
    setoid_rewrite interp_asm_GetReg.
    simpl.
    setoid_rewrite bind_ret_.
    (* Determine next block  *)
    cbn.
    setoid_rewrite bind_ret_.
    replace (fi' _) with (f0 : fin 1) by
      (apply unique_fin; simpl; auto).
    setoid_rewrite bind_bind.
    (* process bb3 *)
    setoid_rewrite den_bb3.
    setoid_rewrite bind_ret_.
    setoid_rewrite bind_bind.
    setoid_rewrite interp_asm_SetReg.
    setoid_rewrite bind_ret_.
    (* process input to bb4 
        (to determine which branch jump came from)
    *)
    unfold from_bif, FromBifunctor_ktree_fin . cbn.
    replace (fi' 0) with (f0 : fin 2).
    2:{ unfold f0.  apply (symmetry jesus). }
    (* process bb4 *)
    setoid_rewrite den_bb4.
    setoid_rewrite bind_bind.
    setoid_rewrite interp_asm_GetReg.
    setoid_rewrite bind_ret_.
    setoid_rewrite interp_asm_SetReg. 
    simpl.
    (* prog1 has been processed
       it resulted in 3 updates to the registers map *)

    (* now prog2 *)
    unfold iprog2.
    setoid_rewrite den_iprog2_point.
    (* process bb1' *)
    setoid_rewrite den_bb1'.
    setoid_rewrite bind_bind.
    setoid_rewrite bind_ret_.
    setoid_rewrite interp_asm_SetReg.
    (* process bb3' *)
    setoid_rewrite den_bb3'.
    setoid_rewrite bind_bind.
    setoid_rewrite bind_ret_.
    setoid_rewrite interp_asm_SetReg.
    simpl.
    (* process bb4' *)
    setoid_rewrite den_bb4'.
    setoid_rewrite bind_bind.
    setoid_rewrite interp_asm_GetReg.
    setoid_rewrite bind_ret_.
    setoid_rewrite interp_asm_SetReg.
    simpl.
    (* prog2 has been processed 
        it resulted in the same 3 updates to the reigsters map *)
    reflexivity.
Qed.

Lemma fuseBlocks : 
    my_EQ iprog2 iprog3.
Proof.
    unfold my_EQ.
    (* interpret prog2 *)
    unfold iprog2.
    setoid_rewrite den_iprog2_point.
    (* interp bb1' *)
    setoid_rewrite den_bb1'.
    interp_asm.
    (* interp bb3' *)
    setoid_rewrite den_bb3'.
    interp_asm.
    (* interp bb4' *)
    setoid_rewrite den_bb4'.
    interp_asm.

    (* interp prog3 *)
    unfold iprog3.
    (* interp bb5 *)
    setoid_rewrite den_bb5.
    interp_asm.
    simpl.
    (* both programs perform the same updates to registers *)
    reflexivity.
Qed.


Lemma constantPropAndFold : my_EQ iprog3 iprog4.
Proof.
    unfold my_EQ.
    (* interp prog3 *)
    unfold iprog3.
    unfold kprog3.
    (* interp bb5 *)
    setoid_rewrite den_bb5_pt.
    interp_asm.
    simpl.

    (* interp prog4 *)
    unfold iprog4.
    unfold kprog4.
    (* interp bb6 *)
    setoid_rewrite den_bb6_pt.
    interp_asm.
    simpl.

    (* program 3 perfroms the updates
        (alist_add 2 5 
        (alist_add 2 4 
        (alist_add 1 0 [])))

       program 4 performs the updates
        (alist_add 2 5 
        (alist_add 1 0 []))

        since 
            r2 := 5 
        shaddows
            r2 :=4
        
        these two updates are equal!

        *)
    reflexivity.
Qed.


Ltac break_match_hyp :=
    match goal with
      | [ H : context [ match ?X with _ => _ end ] |- _] =>
        match type of X with
          | sumbool _ _ => destruct X
          | _ => destruct X eqn:?
        end
    end.
  
  (** [break_match_goal] looks for a [match] construct in your goal, and
      destructs the discriminee, while retaining the information about
      the discriminee's value leading to the branch being taken. *)
  Ltac break_match_goal :=
    match goal with
      | [ |- context [ match ?X with _ => _ end ] ] =>
        match type of X with
          | sumbool _ _ => destruct X
          | _ => destruct X eqn:?
        end
    end.
  
  (** [break_match] breaks a match, either in a hypothesis or in your
      goal. *)
  Ltac break_match := break_match_goal || break_match_hyp.
  
  (** [break_let] breaks a destructuring [let] for a pair. *)
  Ltac break_let :=
    match goal with
      | [ H : context [ (let (_,_) := ?X in _) ] |- _ ] => destruct X eqn:?
      | [ |- context [ (let (_,_) := ?X in _) ] ] => destruct X eqn:?
    end.
  
  Ltac inv_option :=
    match goal with
    | h: Some _ = Some _ |-  _ => inv h
    | h: None   = Some _ |-  _ => inv h
    | h: Some _ = None   |-  _ => inv h
    | h: None   = None   |-  _ => inv h
    end.  

    
Check H0. 
        unfold EQ_registers in H0.
        unfold eq_map in H0.
        pose (H0 0).
        Check mapsto_lookup.
        Check mapsto.
        Print lookup_def.
        unfold lookup_default in e.
        destruct ( lookup 0 regs1) eqn:HX; 
        destruct ( lookup 0 regs2) eqn:HY.
        1:{ 


        destruct ( lookup 0 regs1) eqn:HX in e; 
        destruct ( lookup 0 regs2) eqn:HY in e.
        1:{ }  



        unfold EQ_registers in H.
        unfold eq_map in H.
        pose proof (H 0).
        unfold lookup.
        unfold lookup_default in H0.
        remember (lookup 0 regs1) as x ; setoid_rewrite <- Heqx in H0;
        remember (lookup 0 regs2) as y ; setoid_rewrite <- Heqy in H0.
        case x,y.
        1:{ subst. reflexivity. }
        2:{ pose proof (H 0).         
            unfold lookup_default in H1.
            setoid_rewrite <- Heqx in H1.
            setoid_rewrite <- Heqy in H1.
        }
        break_match ; break_match.
        1:{ subst. auto. rewrite Heqx. rewrite Heqy.
            setoid_rewrite Heqo. setoid_rewrite Heqo0. 
            reflexivity. }
        2:{ subst. setoid_rewrite Heqo in Heqx. inversion Heqx. } 
        3:{ destruct x . constructor. inversion. }
        
        
        reflexivity. }
        inv_option.

  

        remember (lookup 0 regs1) as x.
        remember (lookup 0 regs2) as y.
        remember (lookup 0 regs1) as w in e.  
        remember (lookup 0 regs2) as z in e.
        destruct x ; 
        destruct y ;
        destruct w ;
        destruct z ; try auto ; try constructor.
        5:{ discriminate. }
        destruct w'.
        destruct (lookup 0 regs2) in e.

        destruct x.
        destruct y.
        destruct e.
        1:{ rewrite <- Heqx in e.  }
        Local Transparent lookup.
        unfold lookup.
        
        
        Global Instance my_EQ_refl : Reflexive (my_EQ).
        red.
        intros.
        unfold my_EQ.
        apply ReflexiveH_Reflexive.
        typeclasses eauto.
        Qed.
        
        Global Instance my_EQ_sym : Symmetric (my_EQ).
        red.
        intros.
        unfold my_EQ.
        apply  SymmetricH_Symmetric.
        - typeclasses eauto.
        - exact H.
        Qed. 
        
        Global Instance my_EQ_trans : Transitive (my_EQ).
        red.
        unfold my_EQ.
        intros!.
        eapply TransitiveH_Transitive.
        - typeclasses eauto.
        - exact H.
        - exact H0.
        Qed. 
        
        
        Global Instance my_EQ_eqv : Equivalence (my_EQ).
        constructor; typeclasses eauto.
        Qed.

        Lemma deadbranch : my_EQ iprog1 iprog2.
        Proof. 
             unfold my_EQ.
            unfold iprog1.
            (* unfold iprog1 *)
            setoid_rewrite den_iprog1_point.
            (* process bb1 *)
            setoid_rewrite den_bb1.
            interp_asm.
            simpl.
            (* Determine next block  *)
            replace (fi' _) with (f0 : fin 1) by
              (apply unique_fin; simpl; auto).
            (* process bb3 *)
            setoid_rewrite den_bb3.
            interp_asm.
            simpl.
            (* process input to bb4 
                (to determine which branch jump came from)
            *)
            unfold from_bif, FromBifunctor_ktree_fin . cbn.
            replace (fi' 0) with (f0 : fin 2).
            2:{ unfold f0.  apply (symmetry jesus). }
            (* process bb4 *)
            setoid_rewrite den_bb4.
            interp_asm.
            simpl.
            (* prog1 has been processed
               it resulted in 3 updates to the registers map *)
        
            (* now prog2 *)
            unfold iprog2.
            setoid_rewrite den_iprog2_point.
            (* process bb1' *)
            setoid_rewrite den_bb1'.
            interp_asm.
            (* process bb3' *)
            setoid_rewrite den_bb3'.
            interp_asm.
            (* process bb4' *)
            setoid_rewrite den_bb4'.
            interp_asm.
            (* prog2 has been processed 
                it resulted in the same 3 updates to the reigsters map *)
            reflexivity.
        Qed.



  
(* r3 := 4*)
Definition bb0 : block (fin 1) := 
  after [
      Imov 3 (Oimm 4)
  ] (Bhalt).
  
  (* r3 := r1 + r2*)
  Definition bb1 : block (fin 1) := 
  after [
      Iadd 3 1 (Oreg 2)
  ] (Bhalt).
  (*  Try to show that these instructions are bisimilar
  
   i1:   r3 := 4
  
   i2:   r3 := r1 + r2
  *)
  Definition i1 : instr 
      := Iadd 3 1 (Oreg 2).
  
  Definition i2 : instr 
      := Iadd 3 2 (Oreg 1).
  
  (*
     we can denote each instruction as Itrees using some 
     effect type E where the types of effects we have are
  
     E:= 
      | GetReg 
      | SetReg 
      | Load
      | Store
      | Done 
     *)
  Notation E := Utils.utils.E.
  
  Definition itree_i1 : itree E _ := denote_instr i1.
  Definition itree_i2 : itree E _ := denote_instr i2.
  
  Remark CantProve : 
      itree_i1
  ≈
      itree_i2.
   (* comptue the denotation of both instructions as itrees *)
   unfold itree_i1; unfold itree_i2; unfold denote_instr ; simpl.
   (* try to peel off the first GetReg *)
   eutt_clo_bind_eq.
   (* stuck !*)
   Abort.
  
  (* The problem is that GetReg and SetReg "mean" something..
     
     we have GetReg and SetReg effects.. 
     but we need to run them through an effect handler
  
     thats what interp_asm is for!
     *)
  Check interp_asm.
  Print interp_asm.
  
  Definition interpret {E' A} :
      (memory) ->
      (registers) ->
      itree (Reg +' Memory +' E') A  ->
      itree E' (memory * (registers * A))
   := 
      fun m r prog => 
          interp_asm prog m r.
  
  (*
      interp_asm is is the effect handler for asm programs
      it maps GetReg and SetReg to concrete implementations via 
      the register handler h_reg
  
      h_reg := 
          GetReg x => lookup_def x
        | SetReg x v => insert x v
  
  *)
  Print h_reg.
  
  
  (* We can see if 
      i1:   r3 := r1 + r2
  
      i2:   r3 := r2 + r1 
      
    are bisimilar when we interpret GetReg and SetReg 
  
    to do that, we need to specify the initial memory 
      and register configuration
  
  
   lets say the initial memory is empty 
     and that the initial registers are 
          r1 := 2 
          r2 := 3
          
  
      then the final memory is still empty
      and the final registers are 
          r1 := 2
          r2 := 3
          r3 := 5
          *)
  
  Definition mem : memory := [].
  Definition startReg : registers := 
  [
      (1,2);
      (2,3)
  ].
  Definition endReg : registers := 
  [
      (3,5);
      (1,2);
      (2,3)
  ].
  
  Definition result {E} : itree E (memory * (registers * unit))
      := Ret (mem , (endReg , tt)).
  
  Notation "x ≋ y" := ((eutt rel_asm) x y)(at level 50).
  
  Notation denote_instr := (Asm.denote_instr (E := E)).
  
  Compute interp_asm (denote_instr i1).
  (* we need to interpret these instructions! *)
  Example interpret_i1 : 
      interp_asm (denote_instr i1) mem startReg 
      ≋ 
      result.
  
      (* first denote instruction 1 as an itree*)
      unfold i1.
      unfold denote_instr ; simpl.
      (* then start interpreting the events *)
      rewrite interp_asm_GetReg.
      rewrite interp_asm_GetReg; simpl.
      rewrite interp_asm_SetReg'; cbn.
      (* now all the events have been interpreted 
          see if it equals the result *)
      unfold result.
      unfold startReg.
      unfold alist_add; unfold alist_remove; simpl.
      unfold endReg.
      (* the results match! *)
      reflexivity.
  Qed.
    
  
  
  (* To do that we are going to put i1 and i2 in their own basic blocks*)
  (* 
      bb0:
          r3 := r1 + r2
  *)
  Definition bb0 : block (fin 1) := 
  after [
      Iadd 3 1 (Oreg 2)
  ] (Bhalt).
  
  (* 
      bb1:
          r3 := r2 + r1
  *)
  Definition bb1 : block (fin 1) := 
  after [
      Iadd 3 2 (Oreg 1)
  ] (Bhalt).
  
  (* then we turn those blocks into itrees *)
  Definition bb0_itree : itree E (fin 1) 
    := denote_asm (raw_asm_block bb0) f0.
  
  Definition bb1_itree : itree E (fin 1) 
    := denote_asm (raw_asm_block bb1) f0.
  
  (* but what does bb0 look like as an itree? 
  lets explore that by stepping through the denotation *)
  Lemma den_bb0 : 
      bb0_itree 
  ≈   
  (   lv <- trigger (GetReg 1);;
      rv <- trigger (GetReg 2);;
      trigger (SetReg 3 (lv + rv)));; 
      exit.
  Proof.
     unfold bb0_itree.
      setoid_rewrite raw_asm_block_correct.
      unfold bb0.
      simpl.
      reflexivity.
  Qed.
  
  (*based on that exercise 
      we can see what bb1 is as an itree *)
  Lemma den_bb1 : 
      bb1_itree 
  ≈   
  (  
      lv <- trigger (GetReg 2);;
      rv <- trigger (GetReg 1);;
      trigger (SetReg 3 (lv + rv)));; 
      exit.
  Proof.
   (* lets just use a custom tactic to do this *)
   denBlock bb1_itree bb1.
  Qed.
  
  
  
      
  
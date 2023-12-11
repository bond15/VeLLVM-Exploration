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
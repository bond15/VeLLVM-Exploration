From Coq Require Import
Lists.List
Strings.String
Morphisms
Nat
ZArith
Setoid
RelationClasses.

(*Turning off some of the notation 
helps to see what rules might be helpful*)

From ITree Require Import
    Eq.Eqit
    Basics.Category
    Basics.HeterogeneousRelations
    Basics.Monad
    Basics.CategorySub
    Basics.CategoryOps
    Interp.InterpFacts
    Events.MapDefault
    Events.MapDefaultFacts
    Events.State
    Events.StateFacts
    ITreeMonad
    ITreeFacts
    ITree.

From ExtLib Require Import
    Core.RelDec
    Structures.Monad
    Structures.Maps
    Programming.Show
    Data.Map.FMapAList.

Import CatNotations.
Local Open Scope cat_scope.
Local Open Scope itree_scope.

From ITreeTutorial Require Import 
    Fin 
    Asm 
    AsmCombinators 
    AsmOptimization
    Imp2Asm
    KTreeFin
    Utils_tutorial.

Import ITreeNotations.

Import ListNotations.
Open Scope string_scope.

Import CatNotations.
Local Open Scope cat_scope.
Local Open Scope itree_scope.

From ITreeTutorial Require Import Fin Asm AsmCombinators Utils_tutorial.

From MyProject Require Import 
    Utils.

Notation E := Utils.utils.E.

Module bisimilar_instruction.
Import utils.

Lemma interp_asm_SetReg' {E}  r v mem reg :
  @eutt E _ _ (rel_asm)
       (interp_asm (trigger (SetReg r v)) mem reg)
       (Ret (mem, ((Maps.add r v reg),tt))).
Admitted.

(*  Try to show that these instructions are bisimilar

 i1:   r3 := r1 + r2

 i2:   r3 := r2 + r1
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

Definition itree_i1 : itree E _ := denote_instr i1.
Definition itree_i2 : itree E _ := denote_instr i2.

(* 
 i1:   r3 := r1 + r2

 i2:   r3 := r2 + r1

 It seems like we should be able to say that these to instructions
 are bisimilar..
 let's try..
*)
Remark CantProve : 
    itree_i1
≈
    itree_i2.
 (* comptue the denotation of both instructions as itrees *)
 unfold itree_i1; unfold itree_i2; unfold denote_instr ; simpl.
 (* try to peel off the first GetReg *)
 eutt_clo_bind_eq.
 (* stuck !
 trigger (GetReg 1) ≈ trigger (GetReg 2)

  apply eqit_Vis.
 Error: Unable to unify "subevent nat (GetReg 2)" with "subevent nat (GetReg 1)".
 no way to prove this without saying what GetReg does!
 *)
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

  these instructions do not modify memory
    so the initial and final memory maps are the same

 lets say  the initial registers are 
        r1 := x 
        r2 := y
        

 then the final registers are 
        r1 := x
        r2 := y
        r3 := x + y OR y + x // depending on i1 or i2
        *)
(* summon some variables*)
Variable x : nat.
Variable y : nat.
Variable mem : memory.

Definition startReg : registers := 
[
    (1,x);
    (2,y)
].
Definition endReg_i1 : registers := 
[
    (3,x + y);
    (1,x);
    (2,y)
].

Definition result_i1 {E} : itree E (memory * (registers * unit))
    := Ret (mem , (endReg_i1 , tt)).



(* 
lets check that 
    i1 := r3 := r1 + r2
when
    r1 := x
    r2 := y
evaluates to 

    registers
        r1 := x
        r2 := y
        r3 := x + y
*)
Example evaluate_intruction1 : 
    interp_asm (denote_instr i1) mem startReg
≋ 
    result_i1.
Proof.
    (* first denote instruction 1 as an itree*)
    unfold i1.
    unfold denote_instr ; simpl.
    (* then start interpreting the events *)
    rewrite interp_asm_GetReg ; cbn.
    rewrite interp_asm_GetReg; cbn.
    rewrite interp_asm_SetReg'; cbn.
    unfold startReg.

    (* now all the events have been interpreted 
        see if it equals the result *)
    unfold result_i1; unfold endReg_i1 ; simpl;
    unfold alist_add; unfold alist_remove; simpl.
    (* the results match! *)
    reflexivity.
Qed.

(* now we can finally show 
i1: 
    r3 := r1 + r2
≋ 
i2:
    r3 := r3 + r1

*)
Theorem  bisimilar_i1_i2 : 
    interp_asm (denote_instr i1) mem startReg
≋   
    interp_asm (denote_instr i2) mem startReg.
Proof.
    (* denote the instructions as itrees *)
    unfold i1,i2 ; simpl.
    (* interpret the events *)
    eval_interp ; setoid_rewrite interp_asm_SetReg' ; cbn.
    (* show that the register maps are equal 
       we know that they are since addition is comutative
    *)
    setoid_rewrite plus_comm at 1.
    (* now they are exactly equal! *)
    reflexivity.
Qed.

End bisimilar_instruction.
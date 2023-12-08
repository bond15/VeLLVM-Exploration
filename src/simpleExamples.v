From Coq Require Import
Lists.List
Strings.String
Morphisms
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


Module basicdemo.
Context {E' : Type -> Type}.
Context {HasRegs : Reg -< E'}.
Context {HasMemory : Memory -< E'}.
Context {HasExit : Exit -< E'}.

Definition E := Reg +' Memory +' Exit +' E'.

Notation denote_bk := (denote_bk (E := E)).
Notation denote_bks := (denote_bks (E := E)).
Notation denote_asm := (denote_asm (E := E)).

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

Definition asm0 : ktree_fin E 1 1 := denote_asm (raw_asm_block bb0).
Definition asm1 : ktree_fin E 1 1 := denote_asm (raw_asm_block bb1).

(*   
    initial register state 
    r1 := 2
    r2 := 2
*)
Definition initialRegState : registers := 
[
    (1,2);
    (2,2)
].
(* empty *)
Definition initialMemState : memory := [].


Definition denbb0 : itree E (fin 1) :=  
(
    (v <- Ret 4;; 
    trigger (SetReg 3 v)
    )
    ;; exit
).


Definition denbb1 : itree E (fin 1) :=  
(
    lv <- trigger (GetReg 1);; 
    rv <- trigger (GetReg 2);; 
    trigger (SetReg 3 (lv + rv)));;
    exit.

Definition denbb0NoExit : itree E (fin 1) :=  
(
    v <- Ret 4;; 
    trigger (SetReg 3 v);;
    Ret (f0)
).


Definition denbb1NoExit : itree E (fin 1) :=  
(
    lv <- trigger (GetReg 1);; 
    rv <- trigger (GetReg 2);; 
    trigger (SetReg 3 (lv + rv));;
    Ret f0
).

Lemma bb0Itree : asm0 f0 ≈ denbb0.
Proof.
    unfold asm0.
    unfold denbb0.
    rewrite raw_asm_block_correct.
    unfold denote_bk. 
    reflexivity.
Qed.

Lemma bb1Itree : asm1 f0 ≈ denbb1.
Proof.
    unfold asm1.
    rewrite raw_asm_block_correct.
    unfold denote_bk. 
    cbn.
    reflexivity.
Qed.

Lemma bb0ItreeEQNoExit : asm0 f0 = denbb0NoExit.
Admitted.
Lemma bb1ItreeEQNoExit : asm1 f0 = denbb1NoExit.
Admitted.

(* still no.. using their eq_asm_EQ relation
Lemma foo : @eq_asm_EQ E _ _ _  (raw_asm_block bb0)
(raw_asm_block bb1).
Proof.
    unfold eq_asm_EQ.
    setoid_rewrite denbb0.
*)

(* cheating way *)
Lemma bb0ItreeEQ : asm0 f0 = denbb0.
Admitted.
Lemma bb1ItreeEQ : asm1 f0 = denbb1.
Admitted.

Lemma interp_asm_exit {E} : forall (t : itree (Reg +' Memory +' Exit +' E) unit),
    (interp_asm exit) ≡ (interp_asm (t ;; Ret tt)).
Proof.
    intros.
    unfold EQ_asm.
    intros.
    unfold interp_asm at 1.
    eapply interp_map_proper; try typeclasses eauto ; auto.
    unfold exit.
    setoid_rewrite interp_vis.
    eapply interp_map_proper; try typeclasses eauto ; auto.
Admitted.


Lemma wtf :  
    @interp_asm E nat exit initialMemState initialRegState 
    = Ret (initialMemState,(initialRegState,9)).
Proof.
    intros.
    unfold initialMemState.
    unfold initialRegState.
    unfold interp_asm.
    unfold interp_map.
    unfold interp_state.
Admitted.

Lemma wtf2 : forall r m, 
    @interp_asm E nat exit m r = Ret (m,(r,9)).
Proof.
    intros.
    unfold interp_asm.
    unfold interp_map.
    unfold exit.
    unfold interp_map.
    unfold interp_state.
Admitted.

(*
Lemma foo : forall (t : ktree_fin E 1 1) r m,
    eutt rel_asm 
        (interp_asm (t ;; exit)m r)
        (interp_asm t m r ;; interp_asm exit m r).
*)      

Definition my_EQ (t1 t2 : ktree_fin E 1 1) : Prop :=
    (eutt rel_asm)
        (interp_asm (t1 f0) initialMemState initialRegState)
        (interp_asm (t2 f0) initialMemState initialRegState).

Lemma demo : my_EQ asm0 asm1.
Proof.
    unfold my_EQ.


    (* no exit *)
    rewrite bb0ItreeEQNoExit.
    unfold denbb0NoExit.
    setoid_rewrite bind_ret_l.
    rewrite interp_asm_SetReg.
    setoid_rewrite interp_asm_ret.

    rewrite bb1ItreeEQNoExit.
    unfold denbb1NoExit.
    rewrite interp_asm_GetReg.
    rewrite interp_asm_GetReg.
    rewrite interp_asm_SetReg.
    setoid_rewrite interp_asm_ret.


    rewrite <- eutt_Ret.

    unfold rel_asm.

    constructor.



    (* end no exit*)


    (* still can't do it.....
    setoid_rewrite denbb0. *)
    rewrite bb0ItreeEQ.
    unfold denbb0.
    Check bind_ret_l.
    setoid_rewrite bind_ret_l.
    setoid_rewrite interp_asm_SetReg.
    (* dont know what to do with exit*)

    rewrite bb1ItreeEQ.
    unfold denbb1.
    Check interp_asm_bind.
    

    rewrite interp_asm_bind.
    rewrite interp_asm_bind.
    setoid_rewrite interp_asm_GetReg.

   setoid_rewrite interp_asm_GetReg.

    Print exit.
    


    unfold exit.
    rewrite interp_asm_bind.
    repeat rewrite interp_ret.
       repeat rewrite interp_state_ret.
    unfold interp_asm at 2.
    rewrite interp_vis.

    rewrite interp_asm_bind.
    rewrite interp_asm_bind.
    setoid_rewrite interp_asm_ret.
    


    rewrite bb1ItreeEQ.
    unfold denbb1.
    
    rewrite interp_asm_bind.    
    rewrite interp_asm_bind.


    
    
    rewrite interp_asm_bind.
    rewrite interp_asm_bind.
    setoid_rewrite interp_asm_ret.
   

    rewrite 
    simpl.
    setoid_rewrite interp_asm_SetReg.    
    
    


End basicdemo.
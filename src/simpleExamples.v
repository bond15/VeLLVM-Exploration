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


(* cheating:
    - removing Exit from asm programs
    - force substituting in denoted asm *)
Lemma demo : my_EQ asm0 asm1.
Proof.
    unfold my_EQ.

    (* wait... this works!*)
    Check bb0Itree.
    setoid_rewrite bb0Itree.
    unfold denbb0.
    setoid_rewrite bind_ret_l.
    rewrite interp_asm_SetReg.

    setoid_rewrite bb1Itree.
    unfold denbb1.
    setoid_rewrite bind_bind.
    setoid_rewrite interp_asm_GetReg.
    setoid_rewrite bind_bind.
    setoid_rewrite interp_asm_GetReg.
    rewrite interp_asm_SetReg.

    (* wtf to do with exit *)
    (* evaluation to the rescue 
       we can do this since we provided concrete 
       register and memory states
    *)
    cbn.
    reflexivity.
Qed.
(*  This proof is for the no exit version 
    (* no exit *)
    Restart. (* Undo. *)
    unfold my_EQ.

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
    unfold ret.
    cbn.
    rewrite <- eutt_Ret.
    unfold rel_asm.
    constructor.
    - reflexivity.
    - constructor.
    * reflexivity.
    * reflexivity.
Qed.   
*) 
End basicdemo.


Module deadbranch.

(*
    transformation where (within a block)
    if a register is set to 0
        (track both cases)
    and then that reg is used for the conditional branch
    we can convert the conditional branch into a direct jump

*)

(* prove out a simple example *)

(*
        bb1:
            r1:= 0
            Bbrz r1 bb2 bb3
        /           \ 
    bb2:        bb3:
        r2:= 3       r2:= 4
        Bjmp bb4     Bjmp bb4
        \           /
          bb4:
            r2 := r2 + 1
            BHault


    after dead branch

    bb1:
        r1 := 0
        Bjmp bb3
    bb3:
        r2 := 4
        Bjmp bb4
    bb4:
        r2 := r2 + 1

    bonus: after block fusion


    bb1:
        r1 := 0
        r2 := 4
        r2 := r2 + 1

    bonus: after constant propogation
        r1 := 0
        r2 := 4 + 1

    bonus : after constant folding

        r1 := 0
        r2 := 5
        

*)
Check fS f0.

(* definition of the basic blocks *)
Definition bb1 : block (fin 2):= 
after [
    Imov 1 (Oimm 0)
] (Bbrz 1 f0 (fS f0)).

Definition bb2 : block (fin 1) := 
after [
    Imov 2 (Oimm 3)
] (Bjmp f0).

Definition bb3 : block (fin 1) := 
after [
    Imov 2 (Oimm 4)
] (Bjmp f0).

Definition bb4 : block (fin 1) := 
after [
    Iadd 2 2 (Oimm 1)
] (Bhalt).

(* tying them together as assembly *)

(* block -> asm *)
Definition a_bb1 : asm 1 2 := raw_asm_block bb1.
Definition a_bb2 : asm 1 1 := raw_asm_block bb2.
Definition a_bb3 : asm 1 1 := raw_asm_block bb3.
Definition a_bb4 : asm 2 1 := raw_asm (fun _ => bb4).

(* use asm combinators to link blocks together *)


Definition middle : asm (1 + 1) (1 + 1) 
    := app_asm a_bb2 a_bb3. (* tensor product *)
Definition bottom : asm (1 + 1) 1
    := seq_asm middle a_bb4. (* loop combinator + renaming *)
Definition prog1 : asm 1 1 
    := seq_asm a_bb1 bottom. (* loop combinator + renaming *)

(* idk which is easier to work with 
Definition top : asm 1 (1 + 1)
    := seq_asm a_bb1 middle.
Definition bottom : asm 1 1
    := seq_asm top a_bb4.
*)


(* prog1 defines this assembly program 

        bb1:
            r1:= 0
            Bbrz r1 bb2 bb3
        /           \ 
    bb2:        bb3:
        r2:= 3       r2:= 4
        Bjmp bb4     Bjmp bb4
        \           /
          bb4:
            r2 := r2 + 1
            BHault
*)
(* NOTE: we would need phi nodes here for r2
    LLVM has phi nodes but asm does not

    however, it is not important in this case 
    since we are going to remove the branch
*)

Definition bb1' : block (fin 1) := 
after [
    Imov 1 (Oimm 0)
] (Bjmp f0).

Definition bb3' : block (fin 1) := 
after [
    Imov 2 (Oimm 4)
] (Bjmp f0).

Definition bb4' : block (fin 1) := 
after [
    Iadd 2  2 (Oimm 1)
] (Bhalt).

Definition a_bb1' : asm 1 1 := raw_asm_block bb1'.
Definition a_bb3' : asm 1 1 := raw_asm_block bb3'.
Definition a_bb4' : asm 1 1 := raw_asm_block bb4'.

Definition prog2 : asm 1 1 := seq_asm a_bb1' (seq_asm a_bb3' a_bb4').

(* prog2 defines this assembly program
    bb1':
        r1 := 0
        Bjmp bb3'
    bb3':
        r2 := 4
        Bjmp bb4'
    bb4':
        r2 := r2 + 1 
*)

(* to talk about bisimilarity of these programs
    we need to denote them as itrees

    to do that, we need to determine what effects (E) we are using.

    We will work with an effect E that 
        HasRegs:
            Reg  :=
	            GetReg : reg -> Reg value 
              | SetReg : reg -> value -> Reg unit.

        HasMemory:
            Memory := 
                Load : addr -> Memory value 
              | Store : addr -> value -> Memory unit.

        HasExit 
            Exit :=
                Done : Exit void
    *)
Print Exit.
Context {E' : Type -> Type}.
Context {HasRegs : Reg -< E'}.
Context {HasMemory : Memory -< E'}.
Context {HasExit : Exit -< E'}.
    
Definition E := Reg +' Memory +' Exit +' E'.

Notation denote_bk := (denote_bk (E := E)).
Notation denote_bks := (denote_bks (E := E)).
Notation denote_asm := (denote_asm (E := E)).

Lemma pointfree (p: asm 1 1)(t :ktree_fin E 1 1) :
    denote_asm p ⩯ t ->
    denote_asm p f0 ≈ t f0.
Admitted.

Lemma pointed (k1 k2 :ktree_fin E 1 1) :
     k1 f0 ≈ k2 f0 ->
    k1 ⩯ k2.
Admitted.

(* now we denote the assembly programs as itrees *)
(* NOTE: 
    ktree := (A -> itree E B)
    is a useful abstraction for reasoning
*)
Definition kprog1 : ktree_fin E 1 1 := denote_asm prog1.
Definition kprog2 : ktree_fin E 1 1 := denote_asm prog2.

Definition iprog1 : itree E (fin 1):= kprog1 f0.
Definition iprog2 : itree E (fin 1):= kprog2 f0.


(* helper lemmas - move these*)
Lemma seq_asm_correct {A B C} (ab : asm A B) (bc : asm B C) :
      denote_asm (seq_asm ab bc)
    ⩯ denote_asm ab >>> denote_asm bc.
  Proof.
    unfold seq_asm.
    rewrite loop_asm_correct, relabel_asm_correct, app_asm_correct.
    rewrite fmap_id0, cat_id_r, fmap_swap.
    apply cat_from_loop.
  Qed.

(* helper lemmas for denoting each basic block *)
Lemma den_bb1 : denote_asm a_bb1 ⩯
(fun _ : fin 1 =>
 (
    v <- Ret 0;; 
    trigger (SetReg 1 v));;
    val <- trigger (GetReg 1);;
    (if val : nat
    then Ret f0 
    else Ret (fS f0))).
Proof. 
    unfold a_bb1.
    setoid_rewrite raw_asm_block_correct_lifted.
    unfold bb1.
    reflexivity.
Qed.

Lemma den_bb1_pt : 
    denote_asm a_bb1 f0 
≈
 (
    v <- Ret 0;; 
    trigger (SetReg 1 v));;
    val <- trigger (GetReg 1);;
    (if val : nat
    then Ret f0 
    else Ret (fS f0)).
Proof.
Admitted.


Lemma den_bb2 : denote_asm a_bb2 ⩯
(fun _ : fin 1 => (
    v <- Ret 3;; 
    trigger (SetReg 2 v));; 
    Ret f0).
Proof.
    unfold a_bb2.
    setoid_rewrite raw_asm_block_correct_lifted.
    unfold bb2.
    simpl.
    reflexivity.
Qed.

Lemma den_bb3 : denote_asm a_bb3 ⩯
(fun _ : fin 1 => (
    v <- Ret 4;; 
    trigger (SetReg 2 v));; 
    Ret f0).
Proof.
    unfold a_bb3.
    setoid_rewrite raw_asm_block_correct_lifted.
    unfold bb3.
    simpl.
    reflexivity.
Qed.

Lemma den_bb4 : denote_asm a_bb4 ⩯
(fun _ : fin 2 => 
(
    lv <- trigger (GetReg 2);;
    rv <- Ret 1;; 
    trigger (SetReg 2 (lv + rv))
);; exit).
Proof.
    unfold a_bb4.
    setoid_rewrite raw_asm_correct.
    unfold bb4.
    reflexivity.
Qed.

Lemma den_bb1' : denote_asm a_bb1' ⩯
(fun _ : fin 1 => (
    v <- Ret 0;; 
    trigger (SetReg 1 v));; 
    Ret f0).
Proof.
    unfold a_bb1'.
    setoid_rewrite raw_asm_block_correct_lifted.
    unfold bb1'.
    simpl.
    reflexivity.
Qed.

Lemma den_bb3' : denote_asm a_bb3' ⩯
(fun _ : fin 1 => (
    v <- Ret 4;; 
    trigger (SetReg 2 v));; 
    Ret f0).
Proof.
    unfold a_bb3'.
    setoid_rewrite raw_asm_block_correct_lifted.
    unfold bb3'.
    simpl.
    reflexivity.
Qed.

Lemma den_bb4' : denote_asm a_bb4' ⩯
(fun _ : fin 1 => (
    lv <- trigger (GetReg 2);;
    rv <- Ret 1;; 
    trigger (SetReg 2 (lv + rv)))
    ;; exit).
Proof.
    unfold a_bb4'.
    setoid_rewrite raw_asm_block_correct_lifted.
    unfold bb4'.
    simpl.
    reflexivity.
Qed.

(*  TODO check this claim 
    we cannot prove
        iprog1 ≈ iprog2

    That is because ≈ only says when two programs
        are syntacticaly similar.

    - explain rel_asm
    - explain use concrete initial state
*)

(* make syntax for this *)
Definition my_EQ (t1 t2 : itree E (fin 1)) : Prop :=
    (eutt rel_asm)
        (interp_asm t1 [] [])
        (interp_asm t2 [] []).



Definition foo : itree E (fin 1) := Ret f0.
Definition bar : ktree_fin E 1 1 := fun _ => foo.
Lemma den_prog1 : 
    denote_asm prog1 
⩯ 
    denote_asm a_bb1 >>>
    (bimap 
        (denote_asm a_bb2) 
        (denote_asm a_bb3) >>>
    denote_asm a_bb4).
    unfold prog1.

    setoid_rewrite seq_asm_correct.
    unfold bottom.
    setoid_rewrite seq_asm_correct.
    unfold middle.
    setoid_rewrite app_asm_correct.
    reflexivity.
Qed.

Lemma den_prog1' : 
    denote_asm prog1 f0
≈ 
    (denote_asm a_bb1 >>>
    (bimap 
        (denote_asm a_bb2) 
        (denote_asm a_bb3) >>>
    denote_asm a_bb4)) f0.
Proof.
    apply pointfree.
    apply den_prog1.
Qed.

(* (denote_asm a_bb1 >>>
 (case_ (denote_asm a_bb2 >>> inl_) (denote_asm a_bb3 >>> inr_) >>>
  denote_asm a_bb4)) f0 ≈ Ret f0*)

Lemma asdfasdf : 
    (denote_asm a_bb1' >>> denote_asm a_bb3') f0 
    ≈ 
    (n <- denote_asm a_bb1' f0 ;; denote_asm a_bb3' n) .
Admitted.


Lemma blarg : (denote_asm prog1 f0) ≈  Ret f0.
Proof.
    setoid_rewrite den_prog1'.
    cbn.

    
Admitted.

Print my_EQ.
(* show that the dead branch can be eliminated *)
Lemma deadbranch : my_EQ iprog1 iprog2.
Proof.
    unfold my_EQ.
    unfold iprog1.
    unfold kprog1.
    setoid_rewrite blarg.
    setoid_rewrite interp_asm_ret.
    Check interp_asm.
    Check den_prog1.
    Check den_prog1'.
    setoid_rewrite den_prog1'.
    Check den_bb1.

    setoid_rewrite den_bb1.
    
    (interp_asm
    ((denote_asm a_bb1 >>>
      (bimap (denote_asm a_bb2) (denote_asm a_bb3) >>>
       denote_asm a_bb4)) f0) [] [])




(*iprog1 ≈ iprog2 (eutt eq)
 what is the version for ktrees?
 what is the difference between ≅ (eq_itree eq)
                        and ≈ (eutt eq) ?

"Note that the ⩯ notation in the scope of [ktree] desugars to [eutt_ktree],
      i.e. pointwise [eutt eq]."                        
*)

Remark cantProve : iprog1 ≈ iprog2.
 unfold iprog1.
 unfold kprog1.
 unfold prog1.
 Check raw_asm_block_correct_lifted.
 Check raw_asm_block_correct.
 rewrite seq_asm_correct_lifted.

Print eq_itree.
Remark cantProve : kprog1 ⩯ kprog2.
 unfold kprog1. 
 unfold prog1. (* use ktrees, stupid binder*)

 (*     rewrite raw_asm_block_correct.
    normally i'd use this.. 
    note that it removes the application to "f0"

    How can I get rid of the "f0"?
*)
 rewrite seq_asm_correct.
 
 unfold a_bb1.
 rewrite raw_asm_block_correct_lifted.
 rewrite denote_bk_corect.

 setoid_rewrite loop_asm_correct.
(*  we cannot prove
        iprog1 ≈ iprog2

    That is because ≈ only says when two programs are syntacticaly similar







    Definition rel_asm {B} : memory * (registers * B) -> memory * (registers * B) -> Prop :=
  prod_rel EQ_memory (prod_rel (EQ_registers 0) eq).

we cannot say that iprog1 and iprog2 are bisimilar *)

(* asm programs denoted as ktrees *)

(* concrete initial state *)


Definition my_EQ (t1 t2 : ktree_fin E 1 1) : Prop :=
    (eutt rel_asm)
        (interp_asm (t1 f0) initialMemSta(**
        Definition iprog1_denoted : itree E (fin 1).
        apply iprog1.
        *)te initialRegState)
        (interp_asm (t2 f0) initialMemState initialRegState).



(* is this going to require renaming labels...?*)

Definition deadbranch_branch {lbl} (b : branch lbl) := 
    match b with 
    | Bbrz ()

Definition deadbranch_block {lbl} (bb : block lbl) := 
    match b with 
    | bbb


End deadbranch.

(* 
cruft 

(*


Remark den_prog1 : iprog1 ≈ bar f0.
    unfold iprog1.
    unfold kprog1.
    apply pointfree.

    unfold prog1.

    setoid_rewrite seq_asm_correct.
    setoid_rewrite den_bb1.

    unfold bottom.
    setoid_rewrite seq_asm_correct.
    setoid_rewrite den_bb4.

    unfold middle.
    setoid_rewrite app_asm_correct.
    setoid_rewrite den_bb2.
    setoid_rewrite den_bb3.


    apply pointed.
    
    cbn.


Admitted.

Check to_bif.
Definition den_prog1 : itree E (fin 1):= 
y  <-
    ((v <- Ret 0;; 
      trigger (SetReg 1 v));;
     val <- trigger (GetReg 1);;
    (if val : nat 
    then Ret (f0 : fin (1 + 1)) 
    else Ret ((fS f0): fin (1 + 1)))) : fin (1 + 1);;
(y0 <- to_bif y;;
 case_
   ((fun _ : fin 1 =>
     (v <- Ret 3;; 
     trigger (SetReg 2 v));; 
     Ret f0) >>> inl_)
   ((fun _ : fin 1 =>
     (v <- Ret 4;; 
     trigger (SetReg 2 v));; 
     Ret f0) >>> inr_)
   y0);;
(lv <- trigger (GetReg 2);;
 rv <- Ret 1;; 
 trigger (SetReg 2 (lv + rv)))
 ;; exit.
*)*)
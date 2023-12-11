From Coq Require Import
Lists.List
Strings.String
Morphisms
ZArith
Setoid
Logic.EqdepFacts
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


Module transformationPipeline.
Import utils.


(* 
Demonstrating the correctness 
    of a pipline of transformation on a concrete program
    and abstract memory & register maps.
    
    program1 -- dead branch elim -->
    program2 -- block fusion -->
    program3 -- constant prop & folding -->
    program4

*)

(*
program1:

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
program2:

    bb1:
        r1 := 0
        Bjmp bb3
    bb3:
        r2 := 4
        Bjmp bb4
    bb4:
        r2 := r2 + 1

after block fusion
program3:

    bb5:
        r1 := 0
        r2 := 4
        r2 := r2 + 1

after constant propogation & constant folding 
program4:

    bb6:
        r1 := 0
        r2 := 5
        
*)

(* definition of the basic blocks of program 1 *)
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
    := app_asm a_bb3 a_bb2. (* tensor product *)
Definition bottom : asm (1 + 1) 1
    := seq_asm middle a_bb4. (* loop combinator + renaming *)
Definition prog1 : asm 1 1 
    := seq_asm a_bb1 bottom. (* loop combinator + renaming *)

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

(* define basic blocks of program 2*)
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

(* turn those basic blocks into assembly *)
Definition a_bb1' : asm 1 1 := raw_asm_block bb1'.
Definition a_bb3' : asm 1 1 := raw_asm_block bb3'.
Definition a_bb4' : asm 1 1 := raw_asm_block bb4'.

(* tie the assembly programs together*)
Definition prog2 : asm 1 1 := 
        seq_asm  a_bb1' 
        (seq_asm a_bb3' 
                 a_bb4').

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

Print nat.

(* defining the ambient effect type E 
Context {E' : Type -> Type}.
Context {HasRegs : Reg -< E'}.
Context {HasMemory : Memory -< E'}.
Context {HasExit : Exit -< E'}.
    
Definition E := Reg +' Memory +' Exit +' E'.

Notation denote_bk := (denote_bk (E := E)).
Notation denote_bks := (denote_bks (E := E)).
Notation denote_asm := (denote_asm (E := E)).
*)
Notation E := Utils.utils.E.


(* now we denote the assembly programs as itrees *)
(* NOTE: 
    ktree := (A -> itree E B)
    is a useful abstraction for reasoning
*)
Definition iprog1 : itree E (fin 1):= denote_asm prog1 f0.
Definition iprog2 : itree E (fin 1):= denote_asm prog2 f0.

Ltac denBlock a_bb bb := 
    unfold a_bb;
    setoid_rewrite raw_asm_block_correct;
    unfold bb;
    reflexivity.

(* helper lemmas for denoting each basic block *)
Lemma den_bb1 : 
denote_asm a_bb1 f0
 ≈
 (  v <- Ret 0;; 
    trigger (SetReg 1 v));;
    val <- trigger (GetReg 1);;
    (if val : nat
    then Ret f0 
    else Ret (fS f0)).
Proof. denBlock a_bb1 bb1. Qed.

Lemma den_bb2 : denote_asm a_bb2 f0
≈ 
(   v <- Ret 3;; 
    trigger (SetReg 2 v));; 
    Ret f0.
Proof. denBlock a_bb2 bb2. Qed.


Lemma den_bb3 : denote_asm a_bb3 f0 
≈
(
    v <- Ret 4;; 
    trigger (SetReg 2 v));; 
    Ret f0.
Proof. denBlock a_bb3 bb3. Qed.



Inductive relf0 : fin 2 -> fin 1 ->  Prop :=
| is_f0 : relf0 f0 f0.

Lemma uhg : 
denote_asm (raw_asm (fun _ : fin 2 => bb4)) f0
≈
denote_asm (raw_asm_block bb4) (f0 : fin 1).
Proof.
    cbn.
    eapply eutt_clo_bind.
    - Unshelve. 2:{ exact relf0.  }
Admitted.

Lemma den_bb4 : denote_asm a_bb4 f0 ≈
(
    lv <- trigger (GetReg 2);;
    rv <- Ret 1;; 
    trigger (SetReg 2 (lv + rv))
);; exit.
Proof.
    unfold a_bb4.
    setoid_rewrite uhg.
    setoid_rewrite raw_asm_block_correct.
    cbn.
    reflexivity.
Qed.


Lemma den_bb1' : denote_asm a_bb1' f0 ≈
(
    v <- Ret 0;; 
    trigger (SetReg 1 v));; 
    Ret f0.
Proof. denBlock a_bb1' bb1'. Qed.


Lemma den_bb3' : denote_asm a_bb3' f0
≈
(   v <- Ret 4;; 
    trigger (SetReg 2 v));; 
    Ret f0.
Proof. denBlock a_bb3' bb3'. Qed.


Lemma den_bb4' : denote_asm a_bb4' f0
≈
(
    lv <- trigger (GetReg 2);;
    rv <- Ret 1;; 
    trigger (SetReg 2 (lv + rv)))
    ;; exit.
Proof. denBlock a_bb4' bb4'. Qed.


Notation "x ≋ y" := ((eutt rel_asm) x y)(at level 50).

Definition my_EQ (t1 t2 : itree E (fin 1)) : Prop :=
        (interp_asm t1 [] [])
    ≋
        (interp_asm t2 [] []).


Lemma den_prog1 : 
    denote_asm prog1 f0
≈ 
    (denote_asm a_bb1 >>>
    (bimap 
        (denote_asm a_bb3) 
        (denote_asm a_bb2) >>>
    denote_asm a_bb4)) f0.
Proof.
    apply pointfree.
    unfold prog1.
    setoid_rewrite seq_asm_correct.
    unfold bottom.
    setoid_rewrite seq_asm_correct.
    unfold middle.
    setoid_rewrite app_asm_correct.
    reflexivity.
Qed.

Lemma den_prog2 : 
    denote_asm prog2 
⩯ 
    denote_asm a_bb1' >>>
    (denote_asm a_bb3' >>>
    denote_asm a_bb4').
Proof.
    unfold prog2.
    setoid_rewrite seq_asm_correct.
    setoid_rewrite seq_asm_correct.
    reflexivity.
Qed.

Lemma den_prog2': 
    denote_asm prog2 f0
≈
    (denote_asm a_bb1' >>>
    (denote_asm a_bb3' >>>
    denote_asm a_bb4')) f0.
Proof.
    apply pointed.
    apply den_prog2.
Qed.


Lemma den_iprog1_point : iprog1 ≈ 
(y <- denote_asm a_bb1 f0;;
y0 <- bimap (denote_asm a_bb3) (denote_asm a_bb2) y;;
denote_asm a_bb4 y0).
Proof.    
unfold iprog1.

Local Opaque Asm.denote_asm.
setoid_rewrite den_prog1.

unfold CategoryOps.cat, Cat_sub, CategoryOps.cat, Cat_Kleisli; simpl.
reflexivity.
Qed.

Lemma den_iprog2_point : iprog2 ≈ 
(y <- denote_asm a_bb1' f0;;
y0 <- denote_asm a_bb3' y;;
denote_asm a_bb4' y0).
Proof.    
unfold iprog2.

Local Opaque Asm.denote_asm.
setoid_rewrite den_prog2'.

unfold CategoryOps.cat, Cat_sub, CategoryOps.cat, Cat_Kleisli; simpl.
reflexivity.
Qed.


Lemma jesus : 
@exist nat (fun j : nat => lt j 2) 0
    (Nat.lt_lt_add_r 0 1 1 (Fin.f0_obligation_1 0))
=
 @exist nat (fun j : nat => lt j 2) 0
    (Fin.f0_obligation_1 1).
Proof.
    apply eq_dep_eq_sig.
    assert (
        (Fin.f0_obligation_1 1) 
      = (Nat.lt_lt_add_r 0 1 1 (Fin.f0_obligation_1 0))).
    - admit.
    - rewrite H. reflexivity.
Admitted. 

Ltac getsetRegMem := 
    match goal with 
    (* get reg *)
    | |- (eutt rel_asm 
            (interp_asm 
                (_ <- trigger (GetReg _);; _) 
                _ _)
            _) 
        => setoid_rewrite interp_asm_GetReg
    | |- (eutt rel_asm 
            _ 
            (interp_asm 
                (_ <- trigger (GetReg _);; _) 
                _ _)) 
        => setoid_rewrite interp_asm_GetReg
    (* set reg *)
    | |- (eutt rel_asm
            (interp_asm
                (trigger (SetReg _ _);; _)
                _ _ )
           _)
        => setoid_rewrite interp_asm_SetReg
    | |- (eutt rel_asm
            _ 
            (interp_asm
                (trigger (SetReg _ _);; _)
                _ _ )
            )
    => setoid_rewrite interp_asm_SetReg
    end.

Ltac interp_asm_step :=
    getsetRegMem
||
    setoid_rewrite bind_ret_ 
||
    setoid_rewrite bind_bind.

Ltac interp_asm := 
    repeat interp_asm_step.
        

Definition program1(m : memory)(r : registers) 
    := interp_asm (denote_asm prog1 f0) m r.

Definition program2(m : memory)(r : registers) 
    := interp_asm (denote_asm prog2 f0) m r.

(* this generalizes to all possible 
   register and memory layouts*)
Lemma deadbranch : program1 ≡ program2.
Proof. 
    Local Opaque add. (* so simple and cbn don't reduce map.add*)
    unfold EQ_asm.
    intros.
    (* unfold program 1 *)
    unfold program1.
    setoid_rewrite den_iprog1_point.
    (* process bb1 *)
    setoid_rewrite den_bb1.
    interp_asm.
    (* Determine next block  *)
    replace (fi' _) with (f0 : fin 1) by
      (apply unique_fin; simpl; auto).
    (* process bb3 *)
    setoid_rewrite den_bb3.
    interp_asm.
    (* process input to bb4 
        (to determine which branch jump came from)
    *)
    unfold from_bif, FromBifunctor_ktree_fin . cbn.
    replace (fi' 0) with (f0 : fin 2).
    2:{ unfold f0.  apply (symmetry jesus). }
    (* process bb4 *)
    setoid_rewrite den_bb4.
    interp_asm.
   
    (* prog1 has been processed
       it resulted in 3 updates to the registers map *)

    (* now program 2 *)
    unfold program2.
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
    
    (* show that the register maps are equal
        we know they were initially equal
        we know that prog1 and prog2 
            performed the same updates
        therefore the resulting maps are equal
    *)
    (* first, reduce the total proof obligation to 
        register map equality *)
    unfold interp_asm.
    unfold rel_asm.
    eapply interp_map_proper; try typeclasses eauto; auto ; try reflexivity.
    eapply interp_map_proper; try typeclasses eauto; auto ; try reflexivity.
    (* now it is just a matter of showing that the maps are equal*)
    eapply eq_map_add; try typeclasses eauto; auto.
    eapply eq_map_add; try typeclasses eauto; auto.
    eapply eq_map_add; try typeclasses eauto; auto.
Qed.


(* next step
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


bb5:
    r1 := 0
    r2 := 4
    r2 := r2 + 1

*)

Definition bb5 : block (fin 1) := 
after [
    Imov 1 (Oimm 0);
    Imov 2 (Oimm 4);
    Iadd 2 2 (Oimm 1)
] (Bhalt).

Definition a_bb5 : asm 1 1 
    := raw_asm_block bb5.


Lemma den_bb5 : denote_asm a_bb5 f0
≈
(
    (v <- Ret 0;; trigger (SetReg 1 v));;
    (v <- Ret 4;; trigger (SetReg 2 v));;
    (lv <- trigger (GetReg 2);;
    rv <- Ret 1;; trigger (SetReg 2 (lv + rv)));; exit
).
Proof. denBlock a_bb5 bb5. Qed.

Definition iprog3 : itree E (fin 1)
    := denote_asm a_bb5 f0.

Definition program3 (m: memory)(r : registers)
    := interp_asm (denote_asm a_bb5 f0) m r.

Lemma fuseBlocks : 
    program2 ≡ program3.
Proof.
    Local Opaque add. (* so simple and cbn don't reduce map.add*)
    unfold EQ_asm.
    intros.
    (* interpret program 2 *)
    unfold program2.
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
    unfold program3.
    (* interp bb5 *)
    setoid_rewrite den_bb5.
    interp_asm.
    (* both programs perform the same updates to registers *)
    unfold interp_asm;
    unfold rel_asm;
    repeat (eapply interp_map_proper; try typeclasses eauto; auto ; try reflexivity).
    (* now it is just a matter of showing that the maps are equal*)
    eapply eq_map_add; try typeclasses eauto; auto.
    eapply eq_map_add; try typeclasses eauto; auto.
    eapply eq_map_add; try typeclasses eauto; auto.
Qed.

(* next step 

bb5:
    r1 := 0
    r2 := 4
    r2 := r2 + 1

after constant propogation
and constant folding

bb6: 
    r1 := 0
    r2 := 5

*)

Definition bb6 : block (fin 1) := 
after [
    Imov 1 (Oimm 0);
    Imov 2 (Oimm 5)
] Bhalt.

Definition a_bb6 : asm 1 1 := raw_asm_block bb6.

Lemma den_bb6: denote_asm a_bb6 f0
≈
((v <- Ret 0;; trigger (SetReg 1 v));;
 (v <- Ret 5;; trigger (SetReg 2 v));; 
 exit).
Proof. denBlock a_bb6 bb6. Qed.

Lemma eq_registers (regs1 regs2 : registers): 
EQ_registers 0 regs1 regs2 -> 
@eq_map _ _ _ _ 0
  (add 2
     (lookup_default 2 0
        (add 2 4 (add 1 0 regs1)) + 1)
     (add 2 4 (add 1 0 regs1)))
  (add 2 5 (add 1 0 regs2)).
Proof.
        unfold eq_map.
        intros.
        destruct k.
        1:{ (* k = 0*)
        unfold lookup_default.
        repeat (rewrite lookup_add_neq ; try typeclasses eauto ; try auto).
        assert (lookup 0 regs1 = lookup 0 regs2).
        * admit. 
        * setoid_rewrite H0. reflexivity. }
        destruct k.
        1:{ (* k = 1*)
        unfold lookup_default.
        rewrite lookup_add_neq ; try typeclasses eauto ; try auto. }
        destruct k.
        1:{ (* k = 2*)
        unfold lookup_default.
        rewrite lookup_add_neq ; try typeclasses eauto ; try auto. }
        (* k > 2*)  
        unfold lookup_default.
        repeat (rewrite lookup_add_neq ; try typeclasses eauto ; try auto).
        assert (lookup (S (S (S k))) regs1 = lookup (S (S (S k))) regs2).
        1:{ admit. }
        setoid_rewrite H0.
        reflexivity.
Admitted. 

Definition program4 (m : memory)(r : registers) 
    := interp_asm (denote_asm a_bb6 f0) m r.
    
Lemma constantPropAndFold : 
    program3 ≡ program4.
Proof.
    Local Opaque add.
    Local Opaque lookup. (* so simple and cbn don't reduce map.add*)
    unfold EQ_asm.
    intros.
    (* interp prog3 *)
    unfold program3.
    (* interp bb5 *)
    setoid_rewrite den_bb5.
    interp_asm.

    (* interp prog4 *)
    unfold program4.
    (* interp bb6 *)
    setoid_rewrite den_bb6.
    interp_asm.

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
        unfold interp_asm;
        unfold rel_asm;
        repeat (eapply interp_map_proper; try typeclasses eauto; auto ; try reflexivity).
        (* now it is just a matter of showing that the maps are equal*)

        apply eq_registers.
        exact H0.
Qed.

Global Instance eq_asm_refl {A}: Reflexive (EQ_asm(E := E)(A := A)).
red.
intros.
unfold EQ_asm.
intros.
red.
Print eutt.
eapply ReflexiveH_Reflexive.
(*
eapply ReflexiveH_Reflexive.
typeclasses eauto.
Qed. *)
Abort.

Global Instance eq_asm_trans {A}: Transitive (EQ_asm(E := E)(A := A)).
Admitted.



(* so by transitivity of the my_EQ relation,
    we have prog1 ~ prog4 
    
    *)

Lemma full_transform : program1 ≡ program4.
Proof.
    eapply transitive with (y := program2).
    - apply deadbranch.
    - eapply transitive with (y := program3).
        * apply fuseBlocks.
        * apply constantPropAndFold.
    Unshelve.
    (*apply (@eq_asm_trans (fin 1)).*)
    (* apply (@eq_asm_trans (fin 1)). *)
Admitted.

End transformationPipeline.
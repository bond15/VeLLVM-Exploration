From Coq Require Import
Lists.List
Strings.String
Morphisms
ZArith
Setoid
RelationClasses
Logic.EqdepFacts.

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

Module utils.


(* definitions *)
(*
Context {E : Type -> Type}.
Context {HasRegs : Reg -< E}.
Context {HasMemory : Memory -< E}.
Context {HasExit : Exit -< E}.



(* notation *)
Notation denote_instr := (denote_instr (E := E)).
Notation denote_bk := (denote_bk (E := E)).
Notation denote_bks := (denote_bks (E := E)).
Notation denote_asm := (denote_asm (E := E)).
*)
Context {E' : Type -> Type}.
Context {HasRegs : Reg -< E'}.
Context {HasMemory : Memory -< E'}.
Context {HasExit : Exit -< E'}.
    
Definition E := Reg +' Memory +' Exit +' E'.

Notation denote_bk := (denote_bk (E := E)).
Notation denote_bks := (denote_bks (E := E)).
Notation denote_asm := (denote_asm (E := E)).
Notation "x ≋ y" := ((@eutt E _ _  rel_asm) x y)(at level 50).

(* helper lemmas *)
Lemma seq_asm_correct {A B C} (ab : asm A B) (bc : asm B C) :
      denote_asm (seq_asm ab bc)
    ⩯ denote_asm ab >>> denote_asm bc.
  Proof.
    unfold seq_asm.
    rewrite loop_asm_correct, relabel_asm_correct, app_asm_correct.
    rewrite fmap_id0, cat_id_r, fmap_swap.
    apply cat_from_loop.
  Qed.

Lemma pointfree (p: asm 1 1)(t :ktree_fin E 1 1) :
    denote_asm p ⩯ t ->
    denote_asm p f0 ≈ t f0.
Admitted.

Lemma pointed (k1 k2 :ktree_fin E 1 1) :
     k1 f0 ≈ k2 f0 ->
    k1 ⩯ k2.
Admitted.

(*
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
*)

(* this is infuriating
    it boils down to a proof that f0 : fin 1 = f0 : fin 2 
    but it is dependent type indexed hell
*)
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

(*
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
        ref
*)

(* custom tactics *)

Ltac eutt_clo_bind_eq := 
        apply (@eutt_clo_bind _ _ _ _ _ _ eq).

Global Hint Extern 1 => eutt_clo_bind_eq : myHints.

Ltac denBlock a_bb bb := 
    unfold a_bb;
    setoid_rewrite raw_asm_block_correct;
    unfold bb;
    reflexivity.



(* manually evaluating things can get annoying
    so we can automate that with metaprogramming / tactics!
*)
Ltac getsetRegMem := 
    match goal with 
    (* get reg *)
    | |- (interp_asm 
           (_ <- trigger (GetReg _);; _)  _ _)
           ≋ _
        => setoid_rewrite interp_asm_GetReg
    | |-    _ ≋ 
            (interp_asm 
                (_ <- trigger (GetReg _);; _) 
                _ _)
        => setoid_rewrite interp_asm_GetReg
    (* set reg *)
    | |-    (interp_asm
                (trigger (SetReg _ _);; _) _ _ )
            ≋ _
        => setoid_rewrite interp_asm_SetReg
    | |- 
            _ ≋
            (interp_asm
                (trigger (SetReg _ _);; _)  _ _ )
            
    => setoid_rewrite interp_asm_SetReg
    end.


Ltac getsetRegMem' := 
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
    getsetRegMem'
||
    setoid_rewrite bind_ret_ 
||
    setoid_rewrite bind_bind.

Ltac interp_asm := 
    repeat interp_asm_step.

Ltac eval_interp' :=
        getsetRegMem
    ||
        setoid_rewrite bind_ret_ 
    ||
        setoid_rewrite bind_bind.
    
Ltac eval_interp := 
    repeat eval_interp'.
End utils.

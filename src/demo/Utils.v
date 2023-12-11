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

Ltac eval_interp' :=
        getsetRegMem
    ||
        setoid_rewrite bind_ret_ 
    ||
        setoid_rewrite bind_bind.
    
Ltac eval_interp := 
    repeat eval_interp'.
End utils.

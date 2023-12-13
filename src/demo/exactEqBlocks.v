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

From MyProject Require Import 
    Utils.


Module exact_eq.
Import utils.

(* definition of two basic blocks *)

(* 
    bb0 : 
        r1 := r1 + 1
*)
Definition bb0 : block (fin 1) := 
    after [
        Iadd 1 1 (Oimm 1)
    ] (Bjmp f0).

(* 
    bb1 : 
        r1 := r1 + 1
*)
Definition bb1 : block (fin 1) :=
    after [
        Iadd 1 1 (Oimm 1)
    ] (Bjmp f0).

Definition asm0 : asm 1 1 := raw_asm_block bb0.
Definition asm1 : asm 1 1 := raw_asm_block bb1.

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

(* summon an effect type for this example*)
Notation E := Utils.utils.E.


(* how about showing that asm0 and ams1 are bisimilar?
   first we have to denote them as itrees *)
Definition den_asm0 :itree E (fin 1) := denote_asm asm0 f0.
Definition den_asm1 :itree E (fin 1) := denote_asm asm1 f0.



(* This proof demonstrates that two exacly equal blocks are bilimilar*)
Theorem ExactEqualBlocks : den_asm0 ≈ den_asm1.
Proof.
(* unfold definition of asm programs *)
unfold den_asm0 ; unfold asm0.
unfold den_asm1 ; unfold asm1.

(*denote_asm (raw_asm_block b) f0 ≈ denote_bk b*)
rewrite raw_asm_block_correct;
rewrite raw_asm_block_correct.
(* now we compute the denotation of bb0 and bb1 as 
   interaction trees  *)
unfold bb0;
unfold bb1;
setoid_rewrite denote_after.
unfold denote_br .
unfold denote_list.
unfold traverse_.
unfold denote_instr.
unfold denote_operand;
simpl; repeat setoid_rewrite bind_bind.

(* now that we've computed the denotation 
   we can prove the bisimularity of itrees*)
(* peel off  trigger (GetReg 1)*)
eutt_clo_bind_eq.
1:{ unfold trigger. 
    apply eqit_Vis ;intros.
    apply eqit_Ret.
    reflexivity.
} intros ; subst.

(* peel off Ret 1*)
eutt_clo_bind_eq.
1:{
    apply eqit_Ret.
    reflexivity.
 }
intros; subst.

(* peel off trigger (SetReg ...) *)
unfold trigger ;setoid_rewrite bind_vis.
eapply eqit_Vis ; intros.

(* peel off Ret u*)
eutt_clo_bind_eq.
1:{ 
    apply eqit_Ret.
    reflexivity.
} intros; subst.

(* peel off Ret tt*)
eutt_clo_bind_eq. 
apply eqit_Ret ; reflexivity. 
intros ; subst.

(* finally we have Ret f0*)
apply eqit_Ret.
reflexivity.
Qed.

(* In that last example,
    we manually computed the denotation 
    and the bisimilarity of bb0 and bb1.
    
    Here is a much shorter proof.
    *)
Check eutt_clo_bind.    
Theorem short_ExactEqualBlocks : den_asm0 ≈ den_asm1.
Proof.
(* compute the denotation as itrees *)
unfold den_asm0 ; unfold asm0 ; rewrite raw_asm_block_correct;
unfold den_asm1 ; unfold asm1 ; rewrite raw_asm_block_correct;
unfold denote_bk ; simpl.

(* they are equal!*)
reflexivity.
Qed.

End exact_eq.
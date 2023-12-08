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

(* This serves as a general cheat sheet for the equational theory to reason 
    about Itrees, general interpreters, specific interpreters, 
    ktrees, *)

Module section2.
(* 2.1*)

(* Monad Laws 

    These exist in theories/Basic/Monad
                   theories/Eq/Eqit
*)

Check bind_ret_l.
Check bind_ret_r.
Check bind_bind.

(* Structural Laws *)
Check bind_tau.
Check bind_vis.
Check bind_trigger.
Check unfold_iter.

(* Congruences 
theories/Eq/Eqit

https://github.com/DeepSpec/InteractionTrees/blob/dda104937d79e2052d1a26f6cbe89429245ff743/theories/Eq/Eqit.v#L1060
*)
Check eqit_Tau.
Check eqit_Vis.
Check eqit_Ret.
Check eqit_bind_clo.
Check eutt_clo_bind.
Check eutt_Tau.



(* 2.2 *)

(* figure 6, ktree operations
https://github.com/DeepSpec/InteractionTrees/blob/dda104937d79e2052d1a26f6cbe89429245ff743/theories/Basics/CategoryOps.v#L3C1-L3C1
*)
Check eq2.
Check id_.
Check cat.
Check empty.
Check one.
Check bimap.
Check case_.
Check inl_.
Check inr_.


(* figure 7 laws for ktrees and handlers
https://github.com/DeepSpec/InteractionTrees/blob/dda104937d79e2052d1a26f6cbe89429245ff743/theories/Basics/CategoryKleisliFacts.v
*)
Check compose_pure.
Check assoc_r.
Check unit_l.
Check pure_cat.
Check cat_pure.
Check pure_inl.
Check pure_inr.
Check case_pure.
Check case_l.
Check bimap_id_pure.


End section2.

Module section3.

(* 3.1
 interpreting state events
*)
Check interp_state_ret.
Check interp_state_vis.
Check interp_state_tau.
Check interp_state_trigger_eqit.
Check interp_state_bind.
Check interp_state_trigger.
Check eutt_eq_interp_state_iter.
Check eutt_interp_state_loop.
(* https://github.com/DeepSpec/InteractionTrees/blob/dda104937d79e2052d1a26f6cbe89429245ff743/theories/Events/StateFacts.v#L120
*)

(* 3.2 
monadic interpeters
https://github.com/DeepSpec/InteractionTrees/blob/dda104937d79e2052d1a26f6cbe89429245ff743/theories/Interp/InterpFacts.v#L88
*)
Check interp_ret.
Check interp_tau.
Check interp_vis.
Check interp_trigger.
Check interp_bind.
Check interp_interp.
Check interp_iter.
Check interp_loop.

End section3.


Module section4.

(* iteration and recursion laws 
https://github.com/DeepSpec/InteractionTrees/blob/dda104937d79e2052d1a26f6cbe89429245ff743/theories/Basics/CategoryFacts.v#L753C7-L753C25
theories/basic/categoryfacts
*)
Check iter. 
Check loop. 
Check loop_natural_left.
Check loop_vanishing_1.
Check loop_dinatural.
End section4.


Module tactics.

Print cat_auto.
End tactic.



(* learn loop construct*)
Module loops.

Print loop.
(* loop := inr_ >>> iter (f >>> bimap inl_ (id_ b))

so what are the sub components?
*)

Inductive void : Type -> Type :=.

Definition M := itree void.

Definition k1 : ktree void unit nat 
    := fun tt => Ret 7.
Definition k2 : ktree void nat nat
    := fun n => Ret (n + 1).
Definition k3 : ktree void unit bool 
    := fun tt => Ret true.

Definition k4 : ktree void (unit + nat) nat
    := case_ k1 k2.
    
Eval compute in (inl_ >>> k4).

Definition k5 : ktree void unit nat
    := inl_ >>> k4.

Definition k6 : ktree void unit nat
    := pure (fun tt => 7).

Definition k7 : ktree void (unit + unit) (nat + bool) 
    := bimap k1 k3.


Print bimap.
Check k5.



Definition ex1 : ktree void unit nat := 
    k1 >>> k2.


Definition ex1 (t : M nat) : M (unit * nat) := inr_ unit t.

Print inr_.
Print Inr.

End loops.
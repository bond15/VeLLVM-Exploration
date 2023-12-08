
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

Variant Label : Type := 
| lbb0 : Label
| lbb4 : Label
| lbb7 : Label
| lbb11 : Label
| lbb14 : Label.
(*
Print block.
Print branch.
(* write a simple asm program *)

Definition p1 : block Label := 
    bbb Bhalt.

Definition p2 : block Label := 
    bbi (Iadd 2 3 (Oimm 7)) (bbb Bhalt).


*)

(* 
int foo () {
    int x = 7;
    int y = 0;
    for (int i = 0; i < 7; i++){
        y += x;
    }
    return y;
}

memory map 
  variable  | addres
    x | 0
    y | 8
    i | 16

define dso_local i32 @foo() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 7, i32* %1, align 4
  store i32 0, i32* %2, align 4
  store i32 0, i32* %3, align 4
  br label %4
*)

(* 
    this is dumb..
    store and load can't take registers
    as arguments...
*)

Print fin.
Module exact_eq_example.

(* wtf is with the labels *)
Definition bb0 : block (fin 1) := 
    after [
        Iadd 1 1 (Oimm 1)
    ] (Bjmp f0).

Definition bb1 : block (fin 1) :=
    after [
        Iadd 1 1 (Oimm 1)
    ] (Bjmp f0).

Definition asm0 : asm 1 1 := raw_asm_block bb0.
Definition asm1 : asm 1 1 := raw_asm_block bb1.

Definition asmcombined := app_asm asm0 asm1.
Print denote_asm.

Context {E : Type -> Type}.
  Context {HasRegs : Reg -< E}.
  Context {HasMemory : Memory -< E}.
  Context {HasExit : Exit -< E}.

  Notation denote_bk := (denote_bk (E := E)).
  Notation denote_bks := (denote_bks (E := E)).
  Notation denote_asm := (denote_asm (E := E)).

(* how about showing that asm0 and ams1 are bisimilar?*)
Definition den_asm0 :itree E (fin 1) := denote_asm asm0 f0.
Definition den_asm1 :itree E (fin 1) := denote_asm asm1 f0.

(*≈ means eutt eq *)
(* This proof demonstrates that two exacly equal blocks are bilimilar*)
Lemma ExactEqualBlocks : den_asm0 ≈ den_asm1.
Proof.
(* unfold definition of asm programs *)
unfold den_asm0.
unfold den_asm1.
unfold asm0.
unfold asm1.
(*denote_asm (raw_asm_block b) f0 ≈ denote_bk b*)
rewrite raw_asm_block_correct.
rewrite raw_asm_block_correct.
(* now we can work with just the blocks *)
unfold bb0.
unfold bb1.
reflexivity.
Qed.
(* How can i just say that they are exactly equal?
    maybe use eq in the relation?
    yea that was it.

    rewrite denote_after.
reflexivity.
Qed.
*)

(*repeat setoid_rewrite bind_bind.
apply eqit_bind; try reflexivity. intros _.
    apply eqit_bind; try reflexivity. intros [].
*)

(*eapply eutt_clo_bind; try reflexivity. intros; subst.
*)

(*Check bind_bind.
      rewrite bind_bind.
    eapply eutt_clo_bind.
- cbn. apply eqit_bind. 
* 
reflexivity 
Print eutt. 
*)
End exact_eq_example.

Module help.

(*setup context*)
Context {E : Type -> Type}.
Context {HasRegs : Reg -< E}.
Context {HasMemory : Memory -< E}.
Context {HasExit : Exit -< E}.


Definition prog1 : itree (Reg +' E) nat := Ret 7.
Definition prog2 : itree (Reg +' E) nat := 
( 
    trigger (SetReg 1 7) ;;
    v <- trigger (GetReg 1);;  
    Ret v
).
    
(*
Definition h_reg {E: Type -> Type} `{mapE reg 0 -< E}
  : Reg ~> itree E :=
  fun _ e =>
    match e with
    | GetReg x => lookup_def x
    | SetReg x v => insert x v
    end.
*)

(* SEE here https://github.com/DeepSpec/InteractionTrees/blob/dda104937d79e2052d1a26f6cbe89429245ff743/tutorial/Asm.v#L317C29-L317C64
*)

(* 
alist := fun K V : Type => list (K * V)
reg := nat
value := nat
Definition registers := alist reg value. *)

Definition my_interp {A} (t : itree (Reg +' E) A):
    registers -> itree E (registers * A) :=
    let h := bimap h_reg (id_ _) in 
    let t' := interp h t in 
    fun regs => interp_map t' regs.

Definition example_interp  : itree E (registers * nat)
    := my_interp prog2 [(1,0)].

Compute (burn 100 example_interp).
(* Ret ([(1, 7)], 7) *)

Check prod_rel.
Check relationH.

(* 
EQ_registers = 
fun (d : value) (regs1 regs2 : registers) => eq_map regs1 regs2
	 : value -> registers -> registers -> Prop
*)

Definition rel_regprogs {B} : registers * B -> registers * B -> Prop:= 
    prod_rel (EQ_registers 0) eq.
(* Influenced from line 109 ASM optimizations *)
Definition eq_register_program_denotations_EQ {A B}
    (t1 t2 : Kleisli (itree (Reg +' E)) A B) : Prop :=
    forall (a : A) (regs1 regs2 :registers),
        EQ_registers 0 regs1 regs2 ->
        (eutt rel_regprogs)
            (my_interp (t1 a) regs1)
            (my_interp (t2 a) regs2).

Definition kprog1 : ktree (Reg +' E) unit nat 
    := fun _ => prog1.
Definition kprog2 : ktree (Reg +' E) unit nat 
    := fun _ => prog2.


Lemma my_interp_GetReg {A} f r reg : 
    @eutt E _ _ (@rel_regprogs A)
        (my_interp (val <- trigger (GetReg r) ;; f val) reg)
        ((my_interp (f (lookup_default r 0 reg))) reg).
Admitted.

Lemma my_interp_SetReg { A} f r v  reg :
  @eutt E _ _ (@rel_regprogs A)
       (my_interp (trigger (SetReg r v) ;; f)  reg)
       ((my_interp f)  (Maps.add r v reg)).
Admitted.

Lemma result : eq_register_program_denotations_EQ kprog1 kprog2.
Proof.
    unfold eq_register_program_denotations_EQ. 
    intros x regs1 regs2 eqregs.

    unfold kprog1.
    unfold prog1.
    unfold kprog2.
    unfold prog2.

    setoid_rewrite my_interp_SetReg.
    setoid_rewrite my_interp_GetReg.
    cbn.

    (* almost! *)

    setoid_rewrite interp_ret.

    cbn.
    Check interp_bind.
    unfold my_interp,interp_map.
    unfold id_, Id_Handler, Handler.id_.

    



End help.

Module example2.
(* now show that these to basic blocks are similar 
BB2:
    r1 = add r1 1
    r1 = add r1 1

BB3:
    r1 = add r1 2
*)
Definition bb2 : block (fin 1) := 
    after [
        Iadd 1 1 (Oimm 1);
        Iadd 1 1 (Oimm 1)
    ] (Bjmp f0).

Definition bb3 : block (fin 1) :=
    after [
        Iadd 1 1 (Oimm 2)
    ] (Bjmp f0).


Definition BB2_itree 
    {E}
    {HasExit : Exit -< E}
    {HasReg : Reg -< E}
    {HasMemory: Memory -< E}
    : itree E (fin 1) := denote_asm (raw_asm_block bb2) f0.
Definition BB3_itree 
    {E}
    {HasExit : Exit -< E}
    {HasReg : Reg -< E}
    {HasMemory: Memory -< E}
: itree E (fin 1) := denote_asm (raw_asm_block bb3) f0.


(* hmm may need some tools from ASM Optimization
https://github.com/DeepSpec/InteractionTrees/blob/dda104937d79e2052d1a26f6cbe89429245ff743/tutorial/AsmOptimization.v#L291
*)

(* probably not correct? 
TODO is it correct?
Lemma boring : BB2_itree ≈ BB3_itree.
*)
Check eq_asm_denotations_EQ.
(*
eq_asm_denotations_EQ
	 : ktree (Reg +' Memory +' ?E) ?A ?B ->
       ktree (Reg +' Memory +' ?E) ?A ?B -> Prop
*)

Check interp.
Check interp_asm.

(* helpers? 
Lemma interp_asm_bind {E  R S}
    `{HasExit : Exit -< E}
    `{HasReg : Reg -< E}
    `{HasMemory: Memory -< E}
      (t : itree E R) (k : R -> itree E S) :
    interp_asm  (ITree.bind t k)
  ≅ ITree.bind (interp_asm t) (fun r => interp_asm (k r)).
Proof.
*)

(* see 
Lemma interp_write_one F (handle_io : forall R, ioE R -> itree F R)
  : interp handle_io write_one
  ≈ (xs <- handle_io _ Input;;
     handle_io _ (Output (xs ++ [1]))).
    
 in IntroductionSolutions.v
*)

Check denote_bk bb2. (* itree E (fin 1) *)
Check Reg.
Lemma foo
{E}
    {HasExit : Exit -< E}
    {HasReg : Reg -< E}
    {HasMemory: Memory -< E}
: 
    @eq_asm_denotations_EQ 
        E 
        (fin 1) 
        (fin 1) 
        (fun _ => denote_bk bb2) 
        (fun _ => denote_bk bb3).
Proof.
(* at the asm level 
unfold BB2_itree.
unfold BB3_itree.  
rewrite raw_asm_block_correct.
rewrite raw_asm_block_correct.

now at the block level*)

unfold eq_asm_denotations_EQ.
intros a mem1 mem2 regs1 regs2 EQ_mem EQ_reg.
unfold bb2.
unfold bb3.

(*
unfold denote_bk.
simpl.
 this seems cleaner *)


(* why unfold interp_asm *)
 unfold interp_asm.
    unfold rel_asm.
    eapply interp_map_proper; try typeclasses eauto; auto.
    eapply interp_map_proper; try typeclasses eauto; auto.


rewrite denote_after.
rewrite denote_after.
(* interp (forall T : Type, E T -> M T) -> 
           forall T : Type, itree E T -> M T*)

Check interp_bind.
(* interp f (ITree.bind t k)
       ≅ ITree.bind (interp f t) 
                    (fun r : ?R => 
                       interp f (k r))*)
rewrite interp_bind.
rewrite interp_bind.
Check eutt_clo_bind.
(*
    eutt UU t1 t2 
->
    (forall (u1 : U1) (u2 : U2), 
        UU u1 u2 -> eutt RR (k1 u1) (k2 u2))
 ->
    eutt RR (ITree.bind t1 k1) 
            (ITree.bind t2 k2)
*)
(* this worked because the jumps were the same address*)
(*with (UU := rel_asm)*)
eapply eutt_clo_bind ; try reflexivity.
simpl.
Print h_memory.
(* this now looks like proving 
the equivalence of simple monadic
programs with event handlers*)


rewrite interp_bind.
rewrite interp_bind.

rewrite interp_trigger. cbn.

simpl.


unfold denote_list. 
unfold denote_instr. simpl.

(*breaking abstraction*)
simpl.
rewrite interp_bind.
rewrite interp_bind.
rewrite bind_bind.

unfold trigger.
rewrite interp_vis.
rewrite bind_bind.
simpl.


rewrite interp_bind.

rewrite interp_trigger_h.




Print interp.
(* to the meat of it now,
showing the one instruction has the same effect as the two instructions*)
simpl.
repeat rewrite interp_bind.

rewrite interp_trigger_h.

rewrite interp_state_bind.
rewrite interp_state_trigger_eqit.

rewrite interp_state_bind.

rewrite interp_trigger_h.


rewrite interp_asm_bind.
Print interp_asm.

unfold interp_asm.
unfold MapDefault.interp_map.
repeat rewrite interp_state_ret.

Check interp_asm.
rewrite interp_asm.



unfold bb2.
unfold bb3.
rewrite denote_after.
rewrite denote_after.
Check eqit_bind.
eapply eqit_bind; try reflexivity.
Check bind_bind.
Check denote_list_app.
simpl.
rewrite bind_bind.

cbn.
setoid_rewrite denote_list_app.

End example2.


(* see Imp2Asm line 331
Print bisimilar. *)


(*  
TODO
compare to an ASM to ASM bisimulation relation

Q?
How to convert from a sub (ktree E) to an itree?
    seems like denote_asm is doing something..
    lmao yes.. you denote_asm <asm> f0
    it was under applied, needed to give f0

line 317 Asm
Definition interp_asm {E A} (t : itree (Reg +' Memory +' E) A) :
  memory -> registers -> itree E (memory * (registers * A)) :=
  let h := bimap h_reg (bimap h_memory (id_ _)) in
  let t' := interp h t in
  fun  mem regs => interp_map (interp_map t' regs) mem.

line 331 Imp2AsmCorrect
Definition bisimilar {E} (t1 : itree (ImpState +' E) A) (t2 : itree (Reg +' Memory +' E) B)  :=
    forall g_asm g_imp l,
      Renv g_imp g_asm ->
      eutt state_invariant
           (interp_imp t1 g_imp)
           (interp_asm t2 g_asm l).

line 763 Imp2AsmCorrect
Definition equivalent {E} `{Exit -< E} (s:stmt) (t:asm 1 1) : Prop :=
    bisimilar TT (E := E) (denote_imp s) (denote_asm t f0).


line 822 Imp2AsmCorrect
Theorem compile_correct {E} {HasExit : Exit -< E} (s : stmt) :
    equivalent (E := E) s (compile s).*)
Check eutt (fun _ _ => True) den_asm0.
Print eutt.


Definition a1 : addr := "0".
Definition a2 : addr := "8".
Definition a3 : addr := "16".
Definition bb0 : block Label := 
    after [
        (*Imov 1 (Oimm 0) ;
        Imov 2 (Oimm 8) ;
        Imov 3 (Oimm 16) ;*)
        Istore a1 (Oimm 7);
        Istore a2 (Oimm 0);
        Istore a3 (Oimm 0)
    ] (Bjmp lbb4).


(* 
4:                                                ; preds = %11, %0
  %5 = load i32, i32* %3, align 4
  %6 = icmp slt i32 %5, 7
  br i1 %6, label %7, label %14
*) 
Definition bb4 : block Label := 
    after [
        Iload 5 a3 ;
        ILe 6 5 (Oimm 7) (* le instead of lte*)
    ] (Bbrz 10 lbb7 lbb14).
(*
7:                                                ; preds = %4
  %8 = load i32, i32* %1, align 4
  %9 = load i32, i32* %2, align 4
  %10 = add nsw i32 %9, %8
  store i32 %10, i32* %2, align 4
  br label %11
*)
Definition bb7 : block Label := 
    after [
        Iload 8 a1 ; 
        Iload 9 a2 ;
        Iadd 10 9 (Oreg 8);
        Istore a2 (Oreg 10)
    ] (Bjmp lbb11).

(*
11:                                               ; preds = %7
  %12 = load i32, i32* %3, align 4
  %13 = add nsw i32 %12, 1
  store i32 %13, i32* %3, align 4
  br label %4
*)
Definition bb11 : block Label := 
    after [
        Iload 12 a3 ;
        Iadd 13 12 (Oimm 1) ;
        Istore a3 (Oreg 13)
    ] (Bjmp lbb4).


(*
14:                                               ; preds = %4
  %15 = load i32, i32* %2, align 4
  ret i32 %15
*)
Definition bb14 : block Label := 
    after [
        Iload 15 a2
    ] Bhalt.

Print fin.
Print bks.
Print sub.
Definition bbs : bks 1 1.
unfold bks. intros. 
destruct X. exact bb0.





Definition c : asm 1 1 := 
{|
    internal := 0;
    code := 
|}.
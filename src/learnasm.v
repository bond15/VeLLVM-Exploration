
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



Print inr_.
Print Inr.

End loops.

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

Print eqit_Vis. 

Ltac eutt_clo_bind_eq := 
        apply (@eutt_clo_bind _ _ _ _ _ _ eq).
(*≈ means eutt eq *)
(* This proof demonstrates that two exacly equal blocks are bilimilar*)
Lemma ExactEqualBlocks : den_asm0 ≈ den_asm1.
Proof.
(* unfold definition of asm programs *)
unfold den_asm0 ; unfold asm0.
unfold den_asm1 ; unfold asm1.

(*denote_asm (raw_asm_block b) f0 ≈ denote_bk b*)
rewrite raw_asm_block_correct.
rewrite raw_asm_block_correct.
(* now we compute the denotation of bb0 and bb1 as 
   interaction trees  *)
unfold bb0.
unfold bb1.
setoid_rewrite denote_after.
unfold denote_br .
unfold denote_list.
unfold denote_bk.
unfold traverse_.
unfold denote_instr.
unfold denote_operand.
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

Lemma short_ExactEqualBlocks : den_asm0 ≈ den_asm1.
Proof.
(* compute the denotation as itrees *)
unfold den_asm0 ; unfold asm0 ; rewrite raw_asm_block_correct;
unfold den_asm1 ; unfold asm1 ; rewrite raw_asm_block_correct;
unfold denote_bk ; simpl.

(* they are equal!*)
reflexivity.
Qed.

(*denote_asm
 (raw_asm_block b) f0 ≈ denote_bk b*)
rewrite raw_asm_block_correct.
rewrite raw_asm_block_correct.
(* now we compute the denotation of bb0 and bb1 as 
   interaction trees  *)
unfold bb0.
unfold bb1.
setoid_rewrite denote_after.

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
    v <- trigger(GetReg 1);;
    trigger (SetReg 1 v) ;;
    Ret 7
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

Lemma my_interp_SetReg {A} f r v  reg :
  @eutt E _ _ (@rel_regprogs A)
       (my_interp (trigger (SetReg r v) ;; f)  reg)
       ((my_interp f)  (add r v reg)).
Admitted.

Lemma my_interp_ret {A} (x : A) reg :
    (my_interp (Ret x) reg) ≈ (Ret (reg, x)).
Proof.
    unfold my_interp.
    rewrite interp_ret.
    unfold interp_map.
    rewrite interp_state_ret.
    reflexivity.
Qed.
(*
Context {E': Type -> Type}.
  Notation E := (Reg +' Memory +' E').

Lemma interp_asm_bind: 
    forall {E' R S} 
            (t: itree (Reg +' E) R) 
            (k: R -> itree _ S) 
            (regs : registers) ,
@eutt (Reg +' E') _ _ eq 
      (my_interp (ITree.bind t k) regs)
      (ITree.bind 
        (my_interp t regs) 
        (fun '(regs', x) => my_interp (k x) regs')).

Proof.
intros.
unfold interp_asm.
unfold interp_map. cbn.
repeat rewrite interp_bind.
repeat rewrite interp_state_bind.
repeat rewrite bind_bind.
eapply eutt_clo_bind.
{ reflexivity. }
intros.
rewrite H.
destruct u2 as [g' [l' x]].
reflexivity.
Qed.
*)


(* the trick was to use the constructor tactic *)
Lemma wtf {A B : Type} {R1: relationH A A} {R2 : relationH B B}  {x y : A} {w z : B} :
    R1 x y -> 
    R2 w z -> 
    prod_rel R1 R2 (x , w) (y , z).
Proof.
    intros.
    constructor; simpl ; auto.
Qed.




(* TODO
what LTAC is available to make this simpler?
see theories/EQ/UpToTaus?
*)
Lemma result : eq_register_program_denotations_EQ kprog1 kprog2.
Proof.
    (* unpack the definition of equal register programs *)
    unfold eq_register_program_denotations_EQ. 
    (* introduce variables *)
    intros x regs1 regs2 eqregs.

    (* unpack the program definitons *)
    unfold kprog1.
    unfold prog1.
    unfold kprog2.
    unfold prog2.

    (* interpret the getReg and setReg effects *)
    setoid_rewrite my_interp_GetReg.
    setoid_rewrite my_interp_SetReg.
    
    (* interpret the Ret node*)
    rewrite my_interp_ret.
    rewrite my_interp_ret.

    (* change eutt R (Ret x) (Ret y)
       to
       R (Ret x) (Ret y)
    *)
    rewrite <- eutt_Ret.
    
    (* split the relation and use EQ_registers_add*)
    unfold rel_regprogs.
    constructor ; simpl. 
    (* 7 = 7*)
    2:{reflexivity. }
    (* EQ_registers 0 
        regs1 
        (alist_add 1 
            (lookup_default 1 0 regs2) 
                regs2) *)
    rewrite <- EQ_registers_add ; try reflexivity.
    (* this comes from the Symmetric relations typeclass *)
    apply symmetry.
    exact eqregs.
Qed.
(*
    eapply prod_rel_eqv; try typeclasses eauto.
*)


(* slightly harder proof 
   2 + 2 = 4 

   just Itrees, no assembly yet


*)
Definition prog3 : itree (Reg +' E) nat := 
(
    Ret 4
).
Definition kprog3 : Kleisli (itree (Reg +' E)) unit nat
    := fun _ => prog3.
Definition prog4 : itree (Reg +' E) nat := 
( 
    v1 <- trigger(GetReg 1);;
    v2 <- trigger(GetReg 2);;
    Ret (v1 + v2)
).
Definition kprog4 : Kleisli (itree (Reg +' E)) unit nat
    := fun _ => prog4.

(*   
    initial memory layout
    r1 := 2
    r2 := 2
*)
Definition initialState : registers := 
[
    (1,2);
    (2,2)
].

Definition eq_regprog {A B}
    (t1 t2 : Kleisli (itree (Reg +' E)) A B) : Prop :=
    forall (a : A),
        (eutt rel_regprogs)
            (my_interp (t1 a) initialState)
            (my_interp (t2 a) initialState).


Lemma result2 : eq_regprog kprog3 kprog4.
Proof.
    unfold eq_regprog.
    intros.

    unfold kprog3.
    unfold prog3.
    unfold kprog4.
    unfold prog4.

    rewrite my_interp_GetReg.
    rewrite my_interp_GetReg.

    (*
    huh, don't actually need the setoid version
    setoid_rewrite my_interp_GetReg.
    setoid_rewrite my_interp_GetReg.
    *)

    rewrite my_interp_ret.
    rewrite my_interp_ret.

    rewrite <- eutt_Ret.
    unfold rel_regprogs.
    constructor ; simpl.
    - reflexivity.
    - unfold initialState. 
      cbn.
      reflexivity.
Qed. 
    
(* now write the same program, 
   but using asm syntax 
   store result in r3 
*)
Definition bb0 : block (fin 1) := 
after [
    Imov 3 (Oimm 4)
] (Bhalt).

Definition bb1 : block (fin 1) := 
after [
    Iadd 3 1 (Oreg 2)
] (Bhalt).
(*
Notation denote_bk := (denote_bk (E := E)).
Notation denote_bks := (denote_bks (E := E)).
Notation denote_asm := (denote_asm (E := E)).

*)
(* 
  ktree_fin E A B 
    := 
  sub (ktree E) fin A B
    := 
  fin A -> itree E (fin B)
*)

Definition asm0 : ktree_fin (Reg +' E) 1 1 := denote_asm (raw_asm_block bb0).
Definition asm1 : ktree_fin (Reg +' E) 1 1 := denote_asm (raw_asm_block bb1).


(* use new definition to avoid this nonsense

 (* pose*)
    (*replace a with (@f0 1) by 
     (). *)

    assert (a = f0) as duh by (apply unique_f0).
    rewrite duh.
*)

(* my_interp 
    (denote_asm 
        (raw_asm_block bb) 
        f0) 
    regs
    =
    my_interp
        denote_bk bb
*)
Eval compute in asm1.
Lemma blag {bb : block (fin 1)}{regs} {R}: 
    eutt R
        (my_interp 
            (denote_asm 
                (raw_asm_block bb)
            f0) regs)
        (my_interp
            (denote_bk bb) regs).
Admitted.
(*
            Proof.
(* why 
  setoid_rewrite raw_asm_block_correct.
  *)
    unfold my_interp.
    unfold interp_map.
    repeat setoid_rewrite interp_bind.
    repeat rewrite interp_state_bind.
interp_asm_SetReg'
    rewrite interp_stat
*)





(* how about using a lemma to 
evaluate the denotation of asm program into an itree?*)

(*this one is aggressive, but it works
with rewrites *)
Lemma bb0Itreeeq : asm0 f0 = ((v <- Ret 4;; trigger (SetReg 3 v));; exit).
Proof.
    unfold asm0.
    unfold raw_asm_block.
    unfold raw_asm.
    unfold denote_asm.
    unfold denote_bks.
    simpl.
    unfold loop.
Admitted.   
(*
    cbn.


    (* close, but things are blocked by the "loop" construct*)
    Check loop.
    (*  WRONG DEFINITION (ADDED BASICS.CATEGORYOPS to get the correct definition)
        loop : Handler (?c +' ?a) (?c +' ?b) -> Handler ?a ?b
        where 

        Handler (E F : Type -> Type) := E ~> Itree F.

    *)
    rewrite loop_vanishing_1.

    (* well, probably need to understand this..
        one definition in 455 CategoryOps
    
    
    *)

    unfold loop.
    cat_auto. 
    cbn.

    simpl.

    cbn.
    reflexivity.

(*
    unfold asm0.
    (* compute. too aggresive *)
    reflexivity.
Qed.
*)*)

(* this one "stays in the abstraction"
   but breaks rewrites.*)

Definition denbb0 : itree (Reg +' E) (fin 1)
    :=  ((v <- Ret 4;; trigger (SetReg 3 v));; exit).
Lemma bb0Itree : asm0 f0 ≈ denbb0.
Proof.
    unfold asm0.
    unfold denbb0.
    rewrite raw_asm_block_correct.
    unfold denote_bk. 
    reflexivity.
Qed.

(*
Lemma interpbb0 : my_interp (denote_asm asm0)
≈ my_interp ((v <- Ret 4;; trigger (SetReg 3 v));; exit).
*)

Lemma interpbb0 : 
    (my_interp (asm0 f0) initialState)
    ≈ 
    (my_interp denbb0 initialState).
Admitted.
(*
    congruence.
    (* cant this just be interpeter congruence?....
    is my_interp missing typeclass instances?? *)
    rewrite bb0Itree.
*)


Definition eq_regprog'
    (t1 t2 : ktree_fin (Reg +' E) 1 1) : Prop :=
        (eutt rel_regprogs)
            (my_interp (t1 f0) initialState)
            (my_interp (t2 f0) initialState).
Lemma result3 : eq_regprog' asm0 asm1.
Admitted.
(*
    unfold eq_regprog'.
    rewrite interpbb0.
    unfold denbb0.
    rewrite my_interp_ret.

    unfold asm0.

    unfold denote_asm.
    unfold my_interp.
    rewrite interp_loop.

    (* cheat 
    rewrite bb0Itreeeq.
    rewrite my_interp_bind.
    rewrite my_interp_ret.
    *)

    setoid_rewrite  bb0Itree.

    unfold asm0.
    unfold asm1.

    setoid_rewrite blag.

    unfold bb0.
    unfold bb1.
    cbn.



    unfold denote_asm.





    (* hack and slash following 
    line 397 AsmOpt..v
    *)
    unfold my_interp.
    unfold interp_map.
    repeat setoid_rewrite interp_bind.
    repeat rewrite interp_state_bind.
    repeat apply (@eutt_clo_bind _ _ _ _ _ _ rel_regprogs).
    reflexivity.
    - 
        intros.
        destruct H as [J1 J2].
        unfold CategorySub.from_bif, FromBifunctor_ktree_fin.
        cbn.
        repeat rewrite interp_ret.
        repeat rewrite interp_state_ret.
        apply eqit_Ret.
        constructor; cbn.
        exact J1.
        setoid_rewrite J2.
        reflexivity.
        
    -   
        intros. 
        destruct H as [J1 J2].
        setoid_rewrite J2.
        rewrite interp_state_case.


        compute in J2.
        reflexivity.
        unfold inl_, Inl_Kleisli, lift_ktree_.  




    (* hmm setoid rewriting problems..*)
    Check raw_asm_block_correct.
    (*
        forall b : block (fin ?A),
       denote_asm (raw_asm_block b) f0 ≈ denote_bk b 
    *)

    (* 
        push interp into denotation 
     or 
        evaluate denotation ?
    *)
    setoid_rewrite raw_asm_block_correct.
*)



End help.


Module no_more_my_interp.
(* assuming there are type class issus with my interpeter
  just use the prebaked interpreter for asm *)

  Definition bb0 : block (fin 1) := 
    after [
        Imov 3 (Oimm 4)
    ] (Bhalt).
    
    Definition bb1 : block (fin 1) := 
    after [
        Iadd 3 1 (Oreg 2)
    ] (Bhalt).
    (*
    Notation denote_bk := (denote_bk (E := E)).
    Notation denote_bks := (denote_bks (E := E)).
    Notation denote_asm := (denote_asm (E := E)).
    
    *)
    (* 
      ktree_fin E A B 
        := 
      sub (ktree E) fin A B
        := 
      fin A -> itree E (fin B)
    *)
    
    Definition asm0 : ktree_fin (Reg +' E) 1 1 := denote_asm (raw_asm_block bb0).
    Definition asm1 : ktree_fin (Reg +' E) 1 1 := denote_asm (raw_asm_block bb1).


(* Now use interp_asm instead of my_interp*)





(* In the "help" module,
the relation said both programs 
return the same register assignments.

give a more flexible relation 
that only cares about return value
*)

Module retvalonly.

(*setup context*)
Context {E : Type -> Type}.
Context {HasRegs : Reg -< E}.
Context {HasMemory : Memory -< E}.
Context {HasExit : Exit -< E}.


Definition prog1 : itree (Reg +' E) nat := Ret 7.
Definition prog2 : itree (Reg +' E) nat := 
( 
    v <- trigger(GetReg 1);;
    trigger (SetReg 1 v) ;;
    Ret 7
).
    
Definition my_interp {A} (t : itree (Reg +' E) A):
    registers -> itree E (registers * A) :=
    let h := bimap h_reg (id_ _) in 
    let t' := interp h t in 
    fun regs => interp_map t' regs.

Definition example_interp  : itree E (registers * nat)
    := my_interp prog2 [(1,0)].

Compute (burn 100 example_interp).
(* Ret ([(1, 7)], 7) *)

(* MODIFICATION STARTS HERE *)
Definition rel_regprogs {B} : registers * B -> registers * B -> Prop:= 
    fun p1 p2 => eq (snd p1) (snd p2).    
(*prod_rel (fun r1 r2 => True) eq.*)

(* unsure why but it was in AsmOpt..v*)
Global Hint Unfold rel_regprogs: core.


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

Lemma my_interp_SetReg {A} f r v  reg :
  @eutt E _ _ (@rel_regprogs A)
       (my_interp (trigger (SetReg r v) ;; f)  reg)
       ((my_interp f)  (add r v reg)).
Admitted.

Lemma my_interp_ret {A} (x : A) reg :
    (my_interp (Ret x) reg) ≈ (Ret (reg, x)).
Proof.
    unfold my_interp.
    rewrite interp_ret.
    unfold interp_map.
    rewrite interp_state_ret.
    reflexivity.
Qed.



Lemma result : eq_register_program_denotations_EQ kprog1 kprog2.
Proof.
    (* unpack the definition of equal register programs *)
    unfold eq_register_program_denotations_EQ. 
    (* introduce variables *)
    intros x regs1 regs2 eqregs.

    (* unpack the program definitons *)
    unfold kprog1.
    unfold prog1.
    unfold kprog2.
    unfold prog2.

    (* interpret the getReg and setReg effects *)
    (* PROBLEM STARTS HERE,
       need a Proper instance for the new relation
       to be able to perform setoid rewrite.

       See line 812 of Imp2AsmCorrectness for an example
       not really sure what to do with that..
    *)
    setoid_rewrite my_interp_GetReg.
    setoid_rewrite my_interp_SetReg.
    
    (* interpret the Ret node*)
    rewrite my_interp_ret.
    rewrite my_interp_ret.

    (* change eutt R (Ret x) (Ret y)
       to
       R (Ret x) (Ret y)
    *)
    rewrite <- eutt_Ret.
    
    (* split the relation and use EQ_registers_add*)
    unfold rel_regprogs.
    constructor ; simpl. 
    (* 7 = 7*)
    2:{reflexivity. }
    (* EQ_registers 0 
        regs1 
        (alist_add 1 
            (lookup_default 1 0 regs2) 
                regs2) *)
    rewrite <- EQ_registers_add ; try reflexivity.
    (* this comes from the Symmetric relations typeclass *)
    apply symmetry.
    exact eqregs.
Qed.

End retvalonly.

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
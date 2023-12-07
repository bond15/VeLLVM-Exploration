(*From ITree Require Import
  ITree.
*)
Module learnItrees.
From Coq Require Import
    Strings.String
    List.

Open Scope string_scope. 

CoInductive itree (E : Type -> Type)(R : Type) : Type :=
| Ret (r : R)
| Tau (t : itree E R)
| Vis {A : Type} (e : E A)(k : A -> itree E R).




(* make a simple IO effect type*)

Inductive IO : Type -> Type := 
| Input : IO string
| Output : string -> IO unit.

Inductive void : Type.

CoFixpoint boring : itree IO nat 
  := Ret 42.

CoFixpoint spin : itree IO nat 
  := Tau spin.

CoFixpoint echo : itree IO void 
  := Vis (Input) 
      (fun str => 
        Vis (Output str) 
          (fun _ => echo)).
        
CoFixpoint kill9 : itree IO string 
  := Vis (Input) 
    (fun str => 
      if (str =? "9") 
      then (Ret "done") 
      else kill9).

(*
CoFixpoint echo : itree IO void.
eapply Vis.
- exact Input.
- intros n. eapply Vis. 
    * exact (Output n).
    * intros. exact echo. 
Defined. 
*)
(* This program takes an input n and prints n. repeats forever*)



(*a program which does nothing visible*)
CoFixpoint nada {E : Type -> Type}: itree E void := 
    Tau _ _ nada.

(* this should be equivalent to..*)
CoFixpoint nada' {E : Type -> Type} : itree E void := 
    Tau _ _ (Tau _ _ (Tau _ _ nada')).


Definition isTheAnswer (n : nat) : bool := 
    match n with 
    | 42 => true
    | _ => false    
    end.
(* A program which only terminates after it recieves the number 42*)






(* monadic syntax for Itrees *)
Definition bind {E R S} (t : itree E R) (k : R -> itree E S) : itree E S :=
(cofix bind_ u := match u with
| Ret _ _ r => k r
| Tau _ _ t => Tau _ _ (bind_ t)
| Vis _ _ e k => Vis _ _ e (fun x => bind_ (k x))
end) t.
Definition trigger {E : Type -> Type} {A : Type} (e : E A) : itree E A :=
Vis E A e (fun x => Ret E A x).

CoFixpoint echo : itree IO void := 
    n <- trigger Input ;
    trigger (Output n) ;
    Tau echo.

Theorem compile_correct (s : stmt) : 〚s〛 ≈ 〚(compile s)〛.



(*
Notation "x <- t1 ;; t2" := (bind t1 (fun x => t2))(at level 61, t1 at next level, p pattern, right associativity).

Definition ret x := Ret x.

(* rewrite echo in this syntax *)

CoFixpoint echo2 : itree IO void := 
    n <- trigger Input ;; trigger (Output n) ;; Tau echo2.
*)
(* See ITree.notations
 https://github.com/DeepSpec/InteractionTrees/blob/master/theories/Core/ITreeDefinition.v
*)

End learnItrees.

Module Learn.

From ITree Require Import
    ITree
    ITreeFacts
    Eq.

Import ITreeNotations.


(* example master/examples/ReadmeExample.v*)

(* a custom effect *)
Inductive inputE : Type -> Type := 
| Input : inputE nat.

(* efectful program 
    gets an input and returns it
*)
Definition echo : itree inputE nat := 
    x <- trigger Input;; 
    Ret x.

(* Define a handler for the custom effect 
    whenever Input effect is seen, return n
*)
Definition handler {E} (n : nat) : inputE ~> itree E := 
    fun T e => match e with 
                | Input => Ret n
               end.

(* an interpreter for the echo program
void is empty set
void1 is empty prop*)
Definition echoed (n : nat) : itree void1 nat :=
    interp (handler n) echo.

(* how to run this? *)

Theorem echoed_id : forall n, echoed n ≈ Ret n.
Proof.
intros n.
unfold echoed. 
unfold echo.
rewrite interp_bind.
rewrite interp_trigger.
cbn.
rewrite bind_ret_l.
rewrite interp_ret.
reflexivity.
Qed.

(* Ret 7*)
Compute (burn 2 (echoed 7)).



Print itree. 
Print itree'.

CoFixpoint nada  : itree void1 void := Tau nada.

CoFixpoint nada' : itree void1 void := 
    Tau (Tau (Tau nada')).

(* equivalence up to taus  (eutt)
   weak bisumulation
*)
Check eutt.

(** Strong bisimulation on itrees. If [eqit RR t1 t2],
      we say that [t1] and [t2] are (strongly) bisimilar. As hinted
      at above, bisimilarity can be intuitively thought of as
      equality. 

Axiom bisimulation_is_eq :
  forall {E : Type -> Type} {R : Type} (t1 t2 : itree E R),
    t1 ≅ t2 -> t1 = t2.*)
Check eqit.

From Paco Require Import paco.


Theorem foo : Tau nada' ≈ nada'.
Proof.
Print tau_eutt.
apply tau_eutt. 
Qed.

Theorem bar : nada' ≈ nada.
unfold nada. unfold nada'.
einit. ecofix CIH. edrop.

pose (Tau (Tau (Tau nada')) ≈ nada').

- admit. 
- 


cofix CIH. pcofix CIH. intros. pfold. 


(*pcofix CIH. apply EqTau.
apply EqTau.
Print EqTau.
eapply tau_eutt.

*)





Definition addr : Set := string.
Definition reg : Set := nat.
Definition value : Set := nat.

Variant operand : Set :=
| Oimm (_ : value)
| Oreg (_ : reg).

Variant instr : Set :=
| Imov   (dest : reg) (src : operand)
| Iload  (dest : reg) (addr : addr)
| Istore (addr : addr) (val : operand)
| Iadd   (dest : reg) (src : reg) (o : operand)
...

Variant branch {label : Type} : Type :=
| Bjmp (_ : label)                
| Bbrz (_ : reg) (yes no : label) 
| Bhalt.

Inductive block {label : Type} : Type :=
| bbi (_ : instr) (_ : block)
| bbb (_ : branch label).

Record asm (A B: nat) : Type :=
{
    internal : nat;
    code     : fin (internal + A) -> block (fin (internal + B))
}.


Variant Reg : Type -> Type :=
| GetReg (x : reg) : Reg value
| SetReg (x : reg) (v : value) : Reg unit.

Inductive Memory : Type -> Type :=
| Load  (a : addr) : Memory value
| Store (a : addr) (val : value) : Memory unit.

Definition RegAndMem : Type -> Type := Memory ⊕ Reg.


    Definition denote_operand (o : operand) : itree RegAndMem value :=
      match o with
      | Oimm v => Ret v
      | Oreg v => trigger (GetReg v)
      end.

    Definition denote_instr (i : instr) : itree RegAndMem unit :=
      match i with
      | Iload d addr =>
        val <- trigger (Load addr) ;;
        trigger (SetReg d val)
      | Istore addr v =>
        val <- denote_operand v ;;
        trigger (Store addr val)
      | Imov d s =>
        v <- denote_operand s ;;
        trigger (SetReg d v)
      | Iadd d l r =>
        lv <- trigger (GetReg l) ;;
        rv <- denote_operand r ;;
        trigger (SetReg d (lv + rv))
      ...

    Definition denote_br {B} (b : branch B) : itree RegAndMem B :=
      match b with
      | Bjmp l => Ret l
      | Bbrz v y n =>
        val <- trigger (GetReg v) ;;
        if val:nat then Ret y else Ret n
      | Bhalt => exit
      end.

    Fixpoint denote_bk {B} (b : block B) : itree RegAndMem B :=
      match b with
      | bbi i b =>
        denote_instr i ;; denote_bk b
      | bbb b =>
        denote_br b
      end.

    (** A labelled collection of blocks, [bks], is simply the pointwise
        application of [denote_bk].  Crucially, its denotation is therefore
        a [ktree], whose structure will be useful in the proof of
        the compiler.

        The type [sub (ktree E) fin A B] is shorthand for
        [fin A -> itree E (fin B)], and we can think of them as "continuations"
        with events in E, with input values in [fin A] and output values in [fin B].
        They have a nice algebraic structure, supported by the library,
        including a [loop] combinator that we can use to link collections of
        basic blocks. (See below.) *)
    Definition denote_bks {A B : nat} (bs: bks A B): sub (ktree RegAndMem) fin A B :=
      fun a => denote_bk (bs a).

  (** One can think of an [asm] program as a circuit/diagram where wires
      correspond to jumps/program links.  [denote_bks] computes the meaning of
      each basic block as an [itree] that returns the label of the next block to
      jump to, laying down all our elementary wires.  In order to denote an [asm
      A B] program as a [ktree E A B], it therefore remains to wire all those
      denoted blocks together while hiding the internal labels.  Luckily, that
      is exactly what traced monoidal category are good for.  We therefore
      accomplish this with the same [loop] combinator we used to denote _Imp_'s
      [while] loop.  It directly takes our [denote_bks (code s): ktree E (I + A)
      (I + B)] and hides [I] as desired.  *)
    Definition denote_asm {A B} : asm A B -> sub (ktree RegAndMem) fin A B :=
      fun s => loop (denote_bks (code s)).



  Variant GlobalE (k v:Type) : Type -> Type :=
  | GlobalWrite (id: k) (dv: v): GlobalE k v unit
  | GlobalRead  (id: k): GlobalE k v v.

  Variant LocalE (k v:Type) : Type -> Type :=
  | LocalWrite (id: k) (dv: v): LocalE k v unit
  | LocalRead  (id: k): LocalE k v v.

  Variant StackE (k v:Type) : Type -> Type :=
  | StackPush (args: list (k * v)) : StackE k v unit 
  | StackPop : StackE k v unit. 

  Variant CallE : Type -> Type :=
  | Call        : forall (t:dtyp) (f:uvalue) (args:list uvalue), CallE uvalue.

  Variant ExternalCallE : Type -> Type :=
  | ExternalCall        : forall (t:dtyp) (f:uvalue) (args:list dvalue), ExternalCallE dvalue.

  Variant IntrinsicE : Type -> Type :=
  | Intrinsic : forall (t:dtyp) (f:string) (args:list dvalue), IntrinsicE dvalue.

  Variant MemoryE : Type -> Type :=
  | MemPush : MemoryE unit
  | MemPop  : MemoryE unit
  | Alloca  : forall (t:dtyp),                               (MemoryE dvalue)
  | Load    : forall (t:dtyp)   (a:dvalue),                  (MemoryE uvalue)
  | Store   : forall (a:dvalue) (v:dvalue),                  (MemoryE unit)
  | GEP     : forall (t:dtyp)   (v:dvalue) (vs:list dvalue), (MemoryE dvalue)
  | ItoP    : forall (i:dvalue),                             (MemoryE dvalue)
  | PtoI    : forall (t:dtyp) (a:dvalue),                    (MemoryE dvalue)
  .

  Variant PickE : Type -> Type :=
  | pick (u:uvalue) (P : Prop) : PickE dvalue.

  Variant UBE : Type -> Type :=
  | ThrowUB : string -> UBE void.

  Variant exceptE (Err : Type) : Type -> Type :=
  | Throw : Err -> exceptE Err void.

  Variant DebugE : Type -> Type :=
  | Debug : string -> DebugE unit.
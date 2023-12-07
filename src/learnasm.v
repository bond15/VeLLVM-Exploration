
From Coq Require Import
    Strings.String
    List.

Open Scope string_scope. 
Import ListNotations.

From ITree Require Import
    ITree.

From ITreeTutorial Require Import 
    Fin 
    Asm 
    AsmCombinators 
    Utils_tutorial.


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


(* wtf is with the labels *)
Definition bb0 : block (fin 2) := 
    after [
        Iadd 1 1 (Oimm 1)
    ] (Bjmp (fS f0)).

Definition bb1 : block (fin 2) :=
    after [
        Iadd 1 1 (Oimm 1)
    ] (Bjmp f0).

Definition asm0 := raw_asm_block bb0.
Definition asm1 := raw_asm_block bb1.

Definition asmcombined := loop_asm asm0 asm1.


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
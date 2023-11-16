From Coq Require Import List String ZArith.
(*Print LoadPath.*)
Import ListNotations.
Require Import Vellvm.Syntax.LLVMAst.
Require Import Vellvm.Syntax.CFG.

Definition n : nat := 3.

(*Modifications to get this to parse
  - wrap strings in quotes
  - dropped metadata
  - convert some n%Z to n%N
  - in TLE_Definition.df_instrs, convert the list `cons x xs` into (x , xs)
*)
Definition thing := [TLE_Source_filename "test1"; 
TLE_Datalayout "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"; 
TLE_Target "x86_64-pc-linux-gnu"; 
TLE_Global {|g_ident := (Name "__const.main.A");
             g_typ := (TYPE_Array 10%N (TYPE_I 32%N));
             g_constant := true;
             g_exp := (Some (EXP_Array [((TYPE_I 32%N),(EXP_Integer (0)%Z)); ((TYPE_I 32%N),(EXP_Integer (1)%Z)); ((TYPE_I 32%N),(EXP_Integer (2)%Z)); ((TYPE_I 32%N),(EXP_Integer (3)%Z)); ((TYPE_I 32%N),(EXP_Integer (4)%Z)); ((TYPE_I 32%N),(EXP_Integer (5)%Z)); ((TYPE_I 32%N),(EXP_Integer (6)%Z)); ((TYPE_I 32%N),(EXP_Integer (7)%Z)); ((TYPE_I 32%N),(EXP_Integer (8)%Z)); ((TYPE_I 32%N),(EXP_Integer (9)%Z))]));
             g_linkage := (Some LINKAGE_Private);
             g_visibility := None;
             g_dll_storage := None;
             g_thread_local := None;
             g_unnamed_addr := true;
             g_addrspace := None;
             g_externally_initialized := false;
             g_section := None;
             g_align := (Some 16%Z)|}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "main");
                    dc_type := (TYPE_Function (TYPE_I 32%N) []);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [FNATTR_Attr_grp 0%Z];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [];
  df_instrs := (
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Anon 1%Z), (INSTR_Alloca (TYPE_I 32%N) None (Some 4%Z)));
                               (IId (Anon 2%Z), (INSTR_Alloca (TYPE_Array 10%N (TYPE_I 32%N)) None (Some 16%Z)));
                               (IId (Anon 3%Z), (INSTR_Alloca (TYPE_Array 10%N (TYPE_I 32%N)) None (Some 16%Z)));
                               (IId (Anon 4%Z), (INSTR_Alloca (TYPE_I 32%N) None (Some 4%Z)));
                               (IId (Anon 5%Z), (INSTR_Alloca (TYPE_I 32%N) None (Some 4%Z)));
                               (IVoid 0%Z, (INSTR_Store false ((TYPE_I 32%N), (EXP_Integer (0)%Z)) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 1%Z)))) (Some 4%Z)));
                               (IId (Anon 6%Z), (INSTR_Op (OP_Conversion Bitcast (TYPE_Pointer (TYPE_Array 10%N (TYPE_I 32%N))) (EXP_Ident (ID_Local (Anon 2%Z))) (TYPE_Pointer (TYPE_I 8%N)))));
                               (IId (Anon 7%Z), (INSTR_Op (OP_Conversion Bitcast (TYPE_Pointer (TYPE_Array 10%N (TYPE_I 32%N))) (EXP_Ident (ID_Local (Anon 3%Z))) (TYPE_Pointer (TYPE_I 8%N)))));
                               (IVoid 1%Z, (INSTR_Store false ((TYPE_I 32%N), (EXP_Integer (0)%Z)) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 5%Z)))) (Some 4%Z)));
                               (IVoid 2%Z, (INSTR_Store false ((TYPE_I 32%N), (EXP_Integer (0)%Z)) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 4%Z)))) (Some 4%Z)))];
                  blk_term := TERM_Br_1 (Anon 8%Z);
                  blk_comments := None
                |},[
                {|
                  blk_id := (Anon 8%Z);
                  blk_phis := [];
                  blk_code := [(IId (Anon 9%Z), (INSTR_Load false (TYPE_I 32%N) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 4%Z)))) (Some 4%Z)));
                               (IId (Anon 10%Z), (INSTR_Op (OP_ICmp Slt (TYPE_I 32%N) (EXP_Ident (ID_Local (Anon 9%Z))) (EXP_Integer (10)%Z))))];
                  blk_term := TERM_Br ((TYPE_I 1%N), (EXP_Ident (ID_Local (Anon 10%Z)))) (Anon 11%Z) (Anon 30%Z);
                  blk_comments := None
                |};
                {|
                  blk_id := (Anon 11%Z);
                  blk_phis := [];
                  blk_code := [(IId (Anon 12%Z), (INSTR_Load false (TYPE_I 32%N) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 5%Z)))) (Some 4%Z)));
                               (IId (Anon 13%Z), (INSTR_Op (OP_Conversion Sext (TYPE_I 32%N) (EXP_Ident (ID_Local (Anon 12%Z))) (TYPE_I 64%N))));
                               (IId (Anon 14%Z), (INSTR_Op (OP_GetElementPtr (TYPE_Array 10%N (TYPE_I 32%N)) ((TYPE_Pointer (TYPE_Array 10%N (TYPE_I 32%N))),(EXP_Ident (ID_Local (Anon 2%Z)))) [((TYPE_I 64%N),(EXP_Integer (0)%Z)); ((TYPE_I 64%N),(EXP_Ident (ID_Local (Anon 13%Z))))])));
                               (IId (Anon 15%Z), (INSTR_Load false (TYPE_I 32%N) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 14%Z)))) (Some 4%Z)));
                               (IId (Anon 16%Z), (INSTR_Op (OP_IBinop (Mul false true) (TYPE_I 32%N) (EXP_Ident (ID_Local (Anon 15%Z))) (EXP_Integer (11)%Z))));
                               (IId (Anon 17%Z), (INSTR_Load false (TYPE_I 32%N) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 4%Z)))) (Some 4%Z)));
                               (IId (Anon 18%Z), (INSTR_Op (OP_IBinop (Add false true) (TYPE_I 32%N) (EXP_Ident (ID_Local (Anon 16%Z))) (EXP_Ident (ID_Local (Anon 17%Z))))));
                               (IId (Anon 19%Z), (INSTR_Load false (TYPE_I 32%N) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 4%Z)))) (Some 4%Z)));
                               (IId (Anon 20%Z), (INSTR_Op (OP_Conversion Sext (TYPE_I 32%N) (EXP_Ident (ID_Local (Anon 19%Z))) (TYPE_I 64%N))));
                               (IId (Anon 21%Z), (INSTR_Op (OP_GetElementPtr (TYPE_Array 10%N (TYPE_I 32%N)) ((TYPE_Pointer (TYPE_Array 10%N (TYPE_I 32%N))),(EXP_Ident (ID_Local (Anon 3%Z)))) [((TYPE_I 64%N),(EXP_Integer (0)%Z)); ((TYPE_I 64%N),(EXP_Ident (ID_Local (Anon 20%Z))))])));
                               (IVoid 3%Z, (INSTR_Store false ((TYPE_I 32%N), (EXP_Ident (ID_Local (Anon 18%Z)))) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 21%Z)))) (Some 4%Z)));
                               (IId (Anon 22%Z), (INSTR_Load false (TYPE_I 32%N) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 4%Z)))) (Some 4%Z)));
                               (IId (Anon 23%Z), (INSTR_Op (OP_ICmp Slt (TYPE_I 32%N) (EXP_Ident (ID_Local (Anon 22%Z))) (EXP_Integer (8)%Z))))];
                  blk_term := TERM_Br ((TYPE_I 1%N), (EXP_Ident (ID_Local (Anon 23%Z)))) (Anon 24%Z) (Anon 26%Z);
                  blk_comments := None
                |};
                {|
                  blk_id := (Anon 24%Z);
                  blk_phis := [];
                  blk_code := [(IId (Anon 25%Z), (INSTR_Load false (TYPE_I 32%N) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 4%Z)))) (Some 4%Z)));
                               (IVoid 4%Z, (INSTR_Store false ((TYPE_I 32%N), (EXP_Ident (ID_Local (Anon 25%Z)))) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 5%Z)))) (Some 4%Z)))];
                  blk_term := TERM_Br_1 (Anon 26%Z);
                  blk_comments := None
                |};
                {|
                  blk_id := (Anon 26%Z);
                  blk_phis := [];
                  blk_code := [];
                  blk_term := TERM_Br_1 (Anon 27%Z);
                  blk_comments := None
                |};
                {|
                  blk_id := (Anon 27%Z);
                  blk_phis := [];
                  blk_code := [(IId (Anon 28%Z), (INSTR_Load false (TYPE_I 32%N) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 4%Z)))) (Some 4%Z)));
                               (IId (Anon 29%Z), (INSTR_Op (OP_IBinop (Add false true) (TYPE_I 32%N) (EXP_Ident (ID_Local (Anon 28%Z))) (EXP_Integer (1)%Z))));
                               (IVoid 5%Z, (INSTR_Store false ((TYPE_I 32%N), (EXP_Ident (ID_Local (Anon 29%Z)))) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 4%Z)))) (Some 4%Z)))];
                  blk_term := TERM_Br_1 (Anon 8%Z);
                  blk_comments := None
                |};
                {|
                  blk_id := (Anon 30%Z);
                  blk_phis := [];
                  blk_code := [];
                  blk_term := TERM_Ret ((TYPE_I 32%N), (EXP_Integer (0)%Z));
                  blk_comments := None
                |}]);
                  |}].


Definition modulecfg : mcfg typ := mcfg_of_tle thing.



(* ohh see here https://github.com/vellvm/vellvm/blob/c9b7d6a283c4954b25bf7bcb1b1e54b92b62d699/src/coq/Syntax/SurfaceSyntax.v#L252
*)



                (*
TLE_Attribute_group 0%Z [FNATTR_Noinline; FNATTR_Nounwind; FNATTR_Optnone; FNATTR_Uwtable; FNATTR_Key_value (correctly-rounded-divide-sqrt-fp-math,false); FNATTR_Key_value (disable-tail-calls,false); FNATTR_Key_value (frame-pointer,all); FNATTR_Key_value (less-precise-fpmad,false); FNATTR_Key_value (min-legal-vector-width,0); FNATTR_Key_value (no-infs-fp-math,false); FNATTR_Key_value (no-jump-tables,false); FNATTR_Key_value (no-nans-fp-math,false); FNATTR_Key_value (no-signed-zeros-fp-math,false); FNATTR_Key_value (no-trapping-math,true); FNATTR_Key_value (stack-protector-buffer-size,8); FNATTR_Key_value (target-cpu,x86-64); FNATTR_Key_value (target-features,+cx8,+fxsr,+mmx,+sse,+sse2,+x87); FNATTR_Key_value (unsafe-fp-math,false); FNATTR_Key_value (use-soft-float,false)]; 
TLE_Attribute_group 1%Z [FNATTR_Argmemonly; FNATTR_Nounwind; FNATTR_Willreturn]; 
TLE_Attribute_group 2%Z [FNATTR_Argmemonly; FNATTR_Nounwind; FNATTR_Willreturn; FNATTR_Writeonly]; 
TLE_Metadata (Name "llvm.module.flags") METADATA_Node [METADATA_Id (Anon 0%Z)]; 
TLE_Metadata (Name "llvm.ident") METADATA_Node [METADATA_Id (Anon 1%Z)]; 
TLE_Metadata (Anon 0%Z) METADATA_Node [METADATA_Const ((TYPE_I 32%N), (EXP_Integer (1)%Z)); METADATA_String "wchar_size"; METADATA_Const ((TYPE_I 32%N), (EXP_Integer (4)%Z))]; 
TLE_Metadata (Anon 1%Z) METADATA_Node [METADATA_String "Debian clang version 11.0.1-2"]].
    *)


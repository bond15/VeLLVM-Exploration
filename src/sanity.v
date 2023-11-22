From Coq Require Import List String ZArith.
(*Print LoadPath.*)
Import ListNotations.
Require Import Vellvm.Syntax.
Require Import Vellvm.Syntax.CFG.
Require Import Vellvm.Syntax.TypToDtyp.
Require Import Vellvm.Syntax.DynamicTypes.

Require Import Vellvm.Semantics.TopLevel.

Definition dumb : list(block typ) := [].
Definition sanity := 
    [TLE_Source_filename "sanity.c"; 
TLE_Datalayout "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"; 
TLE_Target "x86_64-pc-linux-gnu"; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "foo");
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
                  blk_code := [];
                  blk_term := TERM_Ret ((TYPE_I 32%N), (EXP_Integer (7)%Z));
                  blk_comments := None
                |}, dumb)
               |} ].

Definition modulecfg : mcfg typ := mcfg_of_tle sanity.

(*stolen form Semantics/TopLevel.v
Definition main_args := [UVALUE_I64 (DynamicValues.Int64.zero);
                        DV.UVALUE_Addr (Addr.null)
                        ].
Definition sanityItree := denote_vellvm m
*)

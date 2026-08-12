From Stdlib Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.16".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "stack.c".
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 22%positive.
Definition ___builtin_annot_intval : ident := 23%positive.
Definition ___builtin_bswap : ident := 7%positive.
Definition ___builtin_bswap16 : ident := 9%positive.
Definition ___builtin_bswap32 : ident := 8%positive.
Definition ___builtin_bswap64 : ident := 6%positive.
Definition ___builtin_cls : ident := 31%positive.
Definition ___builtin_clsl : ident := 32%positive.
Definition ___builtin_clsll : ident := 33%positive.
Definition ___builtin_clz : ident := 10%positive.
Definition ___builtin_clzl : ident := 11%positive.
Definition ___builtin_clzll : ident := 12%positive.
Definition ___builtin_ctz : ident := 13%positive.
Definition ___builtin_ctzl : ident := 14%positive.
Definition ___builtin_ctzll : ident := 15%positive.
Definition ___builtin_debug : ident := 40%positive.
Definition ___builtin_expect : ident := 30%positive.
Definition ___builtin_fabs : ident := 16%positive.
Definition ___builtin_fabsf : ident := 17%positive.
Definition ___builtin_fmadd : ident := 34%positive.
Definition ___builtin_fmax : ident := 38%positive.
Definition ___builtin_fmin : ident := 39%positive.
Definition ___builtin_fmsub : ident := 35%positive.
Definition ___builtin_fnmadd : ident := 36%positive.
Definition ___builtin_fnmsub : ident := 37%positive.
Definition ___builtin_fsqrt : ident := 18%positive.
Definition ___builtin_membar : ident := 24%positive.
Definition ___builtin_memcpy_aligned : ident := 20%positive.
Definition ___builtin_sel : ident := 21%positive.
Definition ___builtin_sqrt : ident := 19%positive.
Definition ___builtin_unreachable : ident := 29%positive.
Definition ___builtin_va_arg : ident := 26%positive.
Definition ___builtin_va_copy : ident := 27%positive.
Definition ___builtin_va_end : ident := 28%positive.
Definition ___builtin_va_start : ident := 25%positive.
Definition ___compcert_i64_dtos : ident := 61%positive.
Definition ___compcert_i64_dtou : ident := 62%positive.
Definition ___compcert_i64_sar : ident := 73%positive.
Definition ___compcert_i64_sdiv : ident := 67%positive.
Definition ___compcert_i64_shl : ident := 71%positive.
Definition ___compcert_i64_shr : ident := 72%positive.
Definition ___compcert_i64_smod : ident := 69%positive.
Definition ___compcert_i64_smulh : ident := 74%positive.
Definition ___compcert_i64_stod : ident := 63%positive.
Definition ___compcert_i64_stof : ident := 65%positive.
Definition ___compcert_i64_udiv : ident := 68%positive.
Definition ___compcert_i64_umod : ident := 70%positive.
Definition ___compcert_i64_umulh : ident := 75%positive.
Definition ___compcert_i64_utod : ident := 64%positive.
Definition ___compcert_i64_utof : ident := 66%positive.
Definition ___compcert_va_composite : ident := 60%positive.
Definition ___compcert_va_float64 : ident := 59%positive.
Definition ___compcert_va_int32 : ident := 57%positive.
Definition ___compcert_va_int64 : ident := 58%positive.
Definition _cons : ident := 1%positive.
Definition _exit : ident := 43%positive.
Definition _free : ident := 42%positive.
Definition _i : ident := 46%positive.
Definition _main : ident := 56%positive.
Definition _malloc : ident := 41%positive.
Definition _n : ident := 51%positive.
Definition _newstack : ident := 45%positive.
Definition _next : ident := 3%positive.
Definition _p : ident := 44%positive.
Definition _pop : ident := 49%positive.
Definition _pop_and_add : ident := 55%positive.
Definition _push : ident := 48%positive.
Definition _push_increasing : ident := 52%positive.
Definition _q : ident := 47%positive.
Definition _s : ident := 54%positive.
Definition _st : ident := 50%positive.
Definition _stack : ident := 4%positive.
Definition _t : ident := 53%positive.
Definition _top : ident := 5%positive.
Definition _value : ident := 2%positive.
Definition _t'1 : ident := 76%positive.
Definition _t'2 : ident := 77%positive.

Definition f_newstack := {|
  fn_return := (tptr (Tstruct _stack noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _stack noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (tulong :: nil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _stack noattr) tulong) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _stack noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr (Tstruct _stack noattr)))
                   tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _stack noattr)))
            (Tstruct _stack noattr)) _top (tptr (Tstruct _cons noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Sreturn (Some (Etempvar _p (tptr (Tstruct _stack noattr))))))))
|}.

Definition f_push := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _stack noattr))) :: (_i, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_q, (tptr (Tstruct _cons noattr))) :: (_t'1, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _cons noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (tulong :: nil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _cons noattr) tulong) :: nil))
    (Sset _q
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _cons noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _q (tptr (Tstruct _cons noattr)))
                   tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _q (tptr (Tstruct _cons noattr)))
            (Tstruct _cons noattr)) _value tint) (Etempvar _i tint))
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _stack noattr)))
                (Tstruct _stack noattr)) _top (tptr (Tstruct _cons noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _q (tptr (Tstruct _cons noattr)))
                (Tstruct _cons noattr)) _next (tptr (Tstruct _cons noattr)))
            (Etempvar _t'2 (tptr (Tstruct _cons noattr)))))
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _stack noattr)))
              (Tstruct _stack noattr)) _top (tptr (Tstruct _cons noattr)))
          (Etempvar _q (tptr (Tstruct _cons noattr))))))))
|}.

Definition f_pop := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _stack noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_q, (tptr (Tstruct _cons noattr))) :: (_i, tint) ::
               (_t'1, (tptr (Tstruct _cons noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _q
    (Efield
      (Ederef (Etempvar _p (tptr (Tstruct _stack noattr)))
        (Tstruct _stack noattr)) _top (tptr (Tstruct _cons noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _q (tptr (Tstruct _cons noattr)))
            (Tstruct _cons noattr)) _next (tptr (Tstruct _cons noattr))))
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _stack noattr)))
            (Tstruct _stack noattr)) _top (tptr (Tstruct _cons noattr)))
        (Etempvar _t'1 (tptr (Tstruct _cons noattr)))))
    (Ssequence
      (Sset _i
        (Efield
          (Ederef (Etempvar _q (tptr (Tstruct _cons noattr)))
            (Tstruct _cons noattr)) _value tint))
      (Ssequence
        (Scall None
          (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
          ((Etempvar _q (tptr (Tstruct _cons noattr))) :: nil))
        (Sreturn (Some (Etempvar _i tint)))))))
|}.

Definition f_push_increasing := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _stack noattr))) :: (_n, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Swhile
    (Ebinop Olt (Etempvar _i tint) (Etempvar _n tint) tint)
    (Ssequence
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))
      (Scall None
        (Evar _push (Tfunction
                      ((tptr (Tstruct _stack noattr)) :: tint :: nil) tvoid
                      cc_default))
        ((Etempvar _st (tptr (Tstruct _stack noattr))) ::
         (Etempvar _i tint) :: nil)))))
|}.

Definition f_pop_and_add := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _stack noattr))) :: (_n, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t, tint) :: (_s, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _s (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Swhile
        (Ebinop Olt (Etempvar _i tint) (Etempvar _n tint) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _pop (Tfunction ((tptr (Tstruct _stack noattr)) :: nil)
                           tint cc_default))
              ((Etempvar _st (tptr (Tstruct _stack noattr))) :: nil))
            (Sset _t (Etempvar _t'1 tint)))
          (Ssequence
            (Sset _s
              (Ebinop Oadd (Etempvar _s tint) (Etempvar _t tint) tint))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint)))))
      (Sreturn (Some (Etempvar _s tint))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_st, (tptr (Tstruct _stack noattr))) :: (_i, tint) ::
               (_t, tint) :: (_s, tint) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _stack noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _newstack (Tfunction nil (tptr (Tstruct _stack noattr))
                          cc_default)) nil)
      (Sset _st (Etempvar _t'1 (tptr (Tstruct _stack noattr)))))
    (Ssequence
      (Scall None
        (Evar _push_increasing (Tfunction
                                 ((tptr (Tstruct _stack noattr)) :: tint ::
                                  nil) tvoid cc_default))
        ((Etempvar _st (tptr (Tstruct _stack noattr))) ::
         (Econst_int (Int.repr 10) tint) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _pop_and_add (Tfunction
                                 ((tptr (Tstruct _stack noattr)) :: tint ::
                                  nil) tint cc_default))
            ((Etempvar _st (tptr (Tstruct _stack noattr))) ::
             (Econst_int (Int.repr 10) tint) :: nil))
          (Sset _s (Etempvar _t'2 tint)))
        (Sreturn (Some (Etempvar _s tint))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _cons Struct
   (Member_plain _value tint ::
    Member_plain _next (tptr (Tstruct _cons noattr)) :: nil)
   noattr ::
 Composite _stack Struct
   (Member_plain _top (tptr (Tstruct _cons noattr)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_cls,
   Gfun(External (EF_builtin "__builtin_cls"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tint :: nil) tint cc_default)) ::
 (___builtin_clsl,
   Gfun(External (EF_builtin "__builtin_clsl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tlong :: nil) tint cc_default)) ::
 (___builtin_clsll,
   Gfun(External (EF_builtin "__builtin_clsll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tlong :: nil) tint cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc, Gfun(External EF_malloc (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_newstack, Gfun(Internal f_newstack)) :: (_push, Gfun(Internal f_push)) ::
 (_pop, Gfun(Internal f_pop)) ::
 (_push_increasing, Gfun(Internal f_push_increasing)) ::
 (_pop_and_add, Gfun(Internal f_pop_and_add)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _pop_and_add :: _push_increasing :: _pop :: _push :: _newstack ::
 _exit :: _free :: _malloc :: ___builtin_debug :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_clsll ::
 ___builtin_clsl :: ___builtin_cls :: ___builtin_expect ::
 ___builtin_unreachable :: ___builtin_va_end :: ___builtin_va_copy ::
 ___builtin_va_arg :: ___builtin_va_start :: ___builtin_membar ::
 ___builtin_annot_intval :: ___builtin_annot :: ___builtin_sel ::
 ___builtin_memcpy_aligned :: ___builtin_sqrt :: ___builtin_fsqrt ::
 ___builtin_fabsf :: ___builtin_fabs :: ___builtin_ctzll ::
 ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll :: ___builtin_clzl ::
 ___builtin_clz :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_bswap64 :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.



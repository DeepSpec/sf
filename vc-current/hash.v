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
  Definition source_file := "hash.c".
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 23%positive.
Definition ___builtin_annot_intval : ident := 24%positive.
Definition ___builtin_bswap : ident := 8%positive.
Definition ___builtin_bswap16 : ident := 10%positive.
Definition ___builtin_bswap32 : ident := 9%positive.
Definition ___builtin_bswap64 : ident := 7%positive.
Definition ___builtin_cls : ident := 32%positive.
Definition ___builtin_clsl : ident := 33%positive.
Definition ___builtin_clsll : ident := 34%positive.
Definition ___builtin_clz : ident := 11%positive.
Definition ___builtin_clzl : ident := 12%positive.
Definition ___builtin_clzll : ident := 13%positive.
Definition ___builtin_ctz : ident := 14%positive.
Definition ___builtin_ctzl : ident := 15%positive.
Definition ___builtin_ctzll : ident := 16%positive.
Definition ___builtin_debug : ident := 41%positive.
Definition ___builtin_expect : ident := 31%positive.
Definition ___builtin_fabs : ident := 17%positive.
Definition ___builtin_fabsf : ident := 18%positive.
Definition ___builtin_fmadd : ident := 35%positive.
Definition ___builtin_fmax : ident := 39%positive.
Definition ___builtin_fmin : ident := 40%positive.
Definition ___builtin_fmsub : ident := 36%positive.
Definition ___builtin_fnmadd : ident := 37%positive.
Definition ___builtin_fnmsub : ident := 38%positive.
Definition ___builtin_fsqrt : ident := 19%positive.
Definition ___builtin_membar : ident := 25%positive.
Definition ___builtin_memcpy_aligned : ident := 21%positive.
Definition ___builtin_sel : ident := 22%positive.
Definition ___builtin_sqrt : ident := 20%positive.
Definition ___builtin_unreachable : ident := 30%positive.
Definition ___builtin_va_arg : ident := 27%positive.
Definition ___builtin_va_copy : ident := 28%positive.
Definition ___builtin_va_end : ident := 29%positive.
Definition ___builtin_va_start : ident := 26%positive.
Definition ___compcert_i64_dtos : ident := 69%positive.
Definition ___compcert_i64_dtou : ident := 70%positive.
Definition ___compcert_i64_sar : ident := 81%positive.
Definition ___compcert_i64_sdiv : ident := 75%positive.
Definition ___compcert_i64_shl : ident := 79%positive.
Definition ___compcert_i64_shr : ident := 80%positive.
Definition ___compcert_i64_smod : ident := 77%positive.
Definition ___compcert_i64_smulh : ident := 82%positive.
Definition ___compcert_i64_stod : ident := 71%positive.
Definition ___compcert_i64_stof : ident := 73%positive.
Definition ___compcert_i64_udiv : ident := 76%positive.
Definition ___compcert_i64_umod : ident := 78%positive.
Definition ___compcert_i64_umulh : ident := 83%positive.
Definition ___compcert_i64_utod : ident := 72%positive.
Definition ___compcert_i64_utof : ident := 74%positive.
Definition ___compcert_va_composite : ident := 68%positive.
Definition ___compcert_va_float64 : ident := 67%positive.
Definition ___compcert_va_int32 : ident := 65%positive.
Definition ___compcert_va_int64 : ident := 66%positive.
Definition _b : ident := 58%positive.
Definition _buckets : ident := 6%positive.
Definition _c : ident := 50%positive.
Definition _cell : ident := 1%positive.
Definition _copy_string : ident := 53%positive.
Definition _count : ident := 3%positive.
Definition _exit : ident := 43%positive.
Definition _get : ident := 59%positive.
Definition _h : ident := 57%positive.
Definition _hash : ident := 51%positive.
Definition _hashtable : ident := 5%positive.
Definition _i : ident := 49%positive.
Definition _incr : ident := 63%positive.
Definition _incr_list : ident := 62%positive.
Definition _incrx : ident := 64%positive.
Definition _key : ident := 2%positive.
Definition _main : ident := 84%positive.
Definition _malloc : ident := 42%positive.
Definition _n : ident := 48%positive.
Definition _new_cell : ident := 55%positive.
Definition _new_table : ident := 54%positive.
Definition _next : ident := 4%positive.
Definition _p : ident := 52%positive.
Definition _r : ident := 61%positive.
Definition _r0 : ident := 60%positive.
Definition _s : ident := 47%positive.
Definition _strcmp : ident := 46%positive.
Definition _strcpy : ident := 45%positive.
Definition _strlen : ident := 44%positive.
Definition _table : ident := 56%positive.
Definition _t'1 : ident := 85%positive.
Definition _t'2 : ident := 86%positive.
Definition _t'3 : ident := 87%positive.
Definition _t'4 : ident := 88%positive.
Definition _t'5 : ident := 89%positive.
Definition _t'6 : ident := 90%positive.

Definition f_hash := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tuint) :: (_i, tulong) :: (_c, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _n (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Sset _c
        (Ederef
          (Ebinop Oadd (Etempvar _s (tptr tschar)) (Etempvar _i tulong)
            (tptr tschar)) tschar))
      (Ssequence
        (Swhile
          (Etempvar _c tint)
          (Ssequence
            (Sset _n
              (Ebinop Oadd
                (Ebinop Omul (Etempvar _n tuint)
                  (Econst_int (Int.repr 65599) tuint) tuint)
                (Ecast (Etempvar _c tint) tuint) tuint))
            (Ssequence
              (Sset _i
                (Ebinop Oadd (Etempvar _i tulong)
                  (Econst_int (Int.repr 1) tint) tulong))
              (Sset _c
                (Ederef
                  (Ebinop Oadd (Etempvar _s (tptr tschar))
                    (Etempvar _i tulong) (tptr tschar)) tschar)))))
        (Sreturn (Some (Etempvar _n tuint)))))))
|}.

Definition f_copy_string := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tulong) :: (_p, (tptr tschar)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _strlen (Tfunction ((tptr tschar) :: nil) tulong cc_default))
      ((Etempvar _s (tptr tschar)) :: nil))
    (Sset _n
      (Ebinop Oadd (Etempvar _t'1 tulong) (Econst_int (Int.repr 1) tint)
        tulong)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _malloc (Tfunction (tulong :: nil) (tptr tvoid) cc_default))
        ((Etempvar _n tulong) :: nil))
      (Sset _p (Etempvar _t'2 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tschar)) tint)
        (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        Sskip)
      (Ssequence
        (Scall None
          (Evar _strcpy (Tfunction ((tptr tschar) :: (tptr tschar) :: nil)
                          (tptr tschar) cc_default))
          ((Etempvar _p (tptr tschar)) :: (Etempvar _s (tptr tschar)) :: nil))
        (Sreturn (Some (Etempvar _p (tptr tschar))))))))
|}.

Definition f_new_table := {|
  fn_return := (tptr (Tstruct _hashtable noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_p, (tptr (Tstruct _hashtable noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (tulong :: nil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _hashtable noattr) tulong) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _hashtable noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _p (tptr (Tstruct _hashtable noattr))) tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 109) tint) tint)
              Sskip
              Sbreak)
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _hashtable noattr)))
                      (Tstruct _hashtable noattr)) _buckets
                    (tarray (tptr (Tstruct _cell noattr)) 109))
                  (Etempvar _i tint) (tptr (tptr (Tstruct _cell noattr))))
                (tptr (Tstruct _cell noattr)))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Sreturn (Some (Etempvar _p (tptr (Tstruct _hashtable noattr))))))))
|}.

Definition f_new_cell := {|
  fn_return := (tptr (Tstruct _cell noattr));
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tschar)) :: (_count, tint) ::
                (_next, (tptr (Tstruct _cell noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _cell noattr))) ::
               (_t'2, (tptr tschar)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (tulong :: nil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _cell noattr) tulong) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _cell noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr (Tstruct _cell noattr)))
                   tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _copy_string (Tfunction ((tptr tschar) :: nil) (tptr tschar)
                               cc_default))
          ((Etempvar _key (tptr tschar)) :: nil))
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
              (Tstruct _cell noattr)) _key (tptr tschar))
          (Etempvar _t'2 (tptr tschar))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
              (Tstruct _cell noattr)) _count tuint) (Etempvar _count tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                (Tstruct _cell noattr)) _next (tptr (Tstruct _cell noattr)))
            (Etempvar _next (tptr (Tstruct _cell noattr))))
          (Sreturn (Some (Etempvar _p (tptr (Tstruct _cell noattr))))))))))
|}.

Definition f_get := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _hashtable noattr))) ::
                (_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, tuint) :: (_b, tuint) ::
               (_p, (tptr (Tstruct _cell noattr))) :: (_t'2, tint) ::
               (_t'1, tuint) :: (_t'4, (tptr tschar)) :: (_t'3, tuint) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _hash (Tfunction ((tptr tschar) :: nil) tuint cc_default))
      ((Etempvar _s (tptr tschar)) :: nil))
    (Sset _h (Etempvar _t'1 tuint)))
  (Ssequence
    (Sset _b
      (Ebinop Omod (Etempvar _h tuint) (Econst_int (Int.repr 109) tint)
        tuint))
    (Ssequence
      (Sset _p
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _table (tptr (Tstruct _hashtable noattr)))
                (Tstruct _hashtable noattr)) _buckets
              (tarray (tptr (Tstruct _cell noattr)) 109)) (Etempvar _b tuint)
            (tptr (tptr (Tstruct _cell noattr))))
          (tptr (Tstruct _cell noattr))))
      (Ssequence
        (Swhile
          (Etempvar _p (tptr (Tstruct _cell noattr)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                      (Tstruct _cell noattr)) _key (tptr tschar)))
                (Scall (Some _t'2)
                  (Evar _strcmp (Tfunction
                                  ((tptr tschar) :: (tptr tschar) :: nil)
                                  tint cc_default))
                  ((Etempvar _t'4 (tptr tschar)) ::
                   (Etempvar _s (tptr tschar)) :: nil)))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                        (Tstruct _cell noattr)) _count tuint))
                  (Sreturn (Some (Etempvar _t'3 tuint))))
                Sskip))
            (Sset _p
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                  (Tstruct _cell noattr)) _next
                (tptr (Tstruct _cell noattr))))))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_incr_list := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r0, (tptr (tptr (Tstruct _cell noattr)))) ::
                (_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _cell noattr))) ::
               (_r, (tptr (tptr (Tstruct _cell noattr)))) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _cell noattr))) ::
               (_t'4, (tptr tschar)) :: (_t'3, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _r (Etempvar _r0 (tptr (tptr (Tstruct _cell noattr)))))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _p
          (Ederef (Etempvar _r (tptr (tptr (Tstruct _cell noattr))))
            (tptr (Tstruct _cell noattr))))
        (Ssequence
          (Sifthenelse (Eunop Onotbool
                         (Etempvar _p (tptr (Tstruct _cell noattr))) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar _new_cell (Tfunction
                                    ((tptr tschar) :: tint ::
                                     (tptr (Tstruct _cell noattr)) :: nil)
                                    (tptr (Tstruct _cell noattr)) cc_default))
                  ((Etempvar _s (tptr tschar)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
                   nil))
                (Sassign
                  (Ederef (Etempvar _r (tptr (tptr (Tstruct _cell noattr))))
                    (tptr (Tstruct _cell noattr)))
                  (Etempvar _t'1 (tptr (Tstruct _cell noattr)))))
              (Sreturn None))
            Sskip)
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                    (Tstruct _cell noattr)) _key (tptr tschar)))
              (Scall (Some _t'2)
                (Evar _strcmp (Tfunction
                                ((tptr tschar) :: (tptr tschar) :: nil) tint
                                cc_default))
                ((Etempvar _t'4 (tptr tschar)) ::
                 (Etempvar _s (tptr tschar)) :: nil)))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                        (Tstruct _cell noattr)) _count tuint))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                        (Tstruct _cell noattr)) _count tuint)
                    (Ebinop Oadd (Etempvar _t'3 tuint)
                      (Econst_int (Int.repr 1) tint) tuint)))
                (Sreturn None))
              Sskip)))))
    (Sset _r
      (Eaddrof
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
            (Tstruct _cell noattr)) _next (tptr (Tstruct _cell noattr)))
        (tptr (tptr (Tstruct _cell noattr)))))))
|}.

Definition f_incr := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _hashtable noattr))) ::
                (_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, tuint) :: (_b, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _hash (Tfunction ((tptr tschar) :: nil) tuint cc_default))
      ((Etempvar _s (tptr tschar)) :: nil))
    (Sset _h (Etempvar _t'1 tuint)))
  (Ssequence
    (Sset _b
      (Ebinop Omod (Etempvar _h tuint) (Econst_int (Int.repr 109) tint)
        tuint))
    (Scall None
      (Evar _incr_list (Tfunction
                         ((tptr (tptr (Tstruct _cell noattr))) ::
                          (tptr tschar) :: nil) tvoid cc_default))
      ((Ebinop Oadd
         (Efield
           (Ederef (Etempvar _table (tptr (Tstruct _hashtable noattr)))
             (Tstruct _hashtable noattr)) _buckets
           (tarray (tptr (Tstruct _cell noattr)) 109)) (Etempvar _b tuint)
         (tptr (tptr (Tstruct _cell noattr)))) ::
       (Etempvar _s (tptr tschar)) :: nil))))
|}.

Definition f_incrx := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _hashtable noattr))) ::
                (_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, tuint) :: (_b, tuint) ::
               (_p, (tptr (Tstruct _cell noattr))) ::
               (_t'3, (tptr (Tstruct _cell noattr))) :: (_t'2, tint) ::
               (_t'1, tuint) :: (_t'6, (tptr tschar)) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct _cell noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _hash (Tfunction ((tptr tschar) :: nil) tuint cc_default))
      ((Etempvar _s (tptr tschar)) :: nil))
    (Sset _h (Etempvar _t'1 tuint)))
  (Ssequence
    (Sset _b
      (Ebinop Omod (Etempvar _h tuint) (Econst_int (Int.repr 109) tint)
        tuint))
    (Ssequence
      (Sset _p
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _table (tptr (Tstruct _hashtable noattr)))
                (Tstruct _hashtable noattr)) _buckets
              (tarray (tptr (Tstruct _cell noattr)) 109)) (Etempvar _b tuint)
            (tptr (tptr (Tstruct _cell noattr))))
          (tptr (Tstruct _cell noattr))))
      (Ssequence
        (Swhile
          (Etempvar _p (tptr (Tstruct _cell noattr)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                      (Tstruct _cell noattr)) _key (tptr tschar)))
                (Scall (Some _t'2)
                  (Evar _strcmp (Tfunction
                                  ((tptr tschar) :: (tptr tschar) :: nil)
                                  tint cc_default))
                  ((Etempvar _t'6 (tptr tschar)) ::
                   (Etempvar _s (tptr tschar)) :: nil)))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                          (Tstruct _cell noattr)) _count tuint))
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                          (Tstruct _cell noattr)) _count tuint)
                      (Ebinop Oadd (Etempvar _t'5 tuint)
                        (Econst_int (Int.repr 1) tint) tuint)))
                  (Sreturn None))
                Sskip))
            (Sset _p
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                  (Tstruct _cell noattr)) _next
                (tptr (Tstruct _cell noattr))))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _table (tptr (Tstruct _hashtable noattr)))
                      (Tstruct _hashtable noattr)) _buckets
                    (tarray (tptr (Tstruct _cell noattr)) 109))
                  (Etempvar _b tuint) (tptr (tptr (Tstruct _cell noattr))))
                (tptr (Tstruct _cell noattr))))
            (Scall (Some _t'3)
              (Evar _new_cell (Tfunction
                                ((tptr tschar) :: tint ::
                                 (tptr (Tstruct _cell noattr)) :: nil)
                                (tptr (Tstruct _cell noattr)) cc_default))
              ((Etempvar _s (tptr tschar)) ::
               (Econst_int (Int.repr 1) tint) ::
               (Etempvar _t'4 (tptr (Tstruct _cell noattr))) :: nil)))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _table (tptr (Tstruct _hashtable noattr)))
                    (Tstruct _hashtable noattr)) _buckets
                  (tarray (tptr (Tstruct _cell noattr)) 109))
                (Etempvar _b tuint) (tptr (tptr (Tstruct _cell noattr))))
              (tptr (Tstruct _cell noattr)))
            (Etempvar _t'3 (tptr (Tstruct _cell noattr)))))))))
|}.

Definition composites : list composite_definition :=
(Composite _cell Struct
   (Member_plain _key (tptr tschar) :: Member_plain _count tuint ::
    Member_plain _next (tptr (Tstruct _cell noattr)) :: nil)
   noattr ::
 Composite _hashtable Struct
   (Member_plain _buckets (tarray (tptr (Tstruct _cell noattr)) 109) :: nil)
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
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_strlen,
   Gfun(External (EF_external "strlen"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tschar) :: nil) tulong cc_default)) ::
 (_strcpy,
   Gfun(External (EF_external "strcpy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xptr
                     cc_default)) ((tptr tschar) :: (tptr tschar) :: nil)
     (tptr tschar) cc_default)) ::
 (_strcmp,
   Gfun(External (EF_external "strcmp"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: (tptr tschar) :: nil)
     tint cc_default)) :: (_hash, Gfun(Internal f_hash)) ::
 (_copy_string, Gfun(Internal f_copy_string)) ::
 (_new_table, Gfun(Internal f_new_table)) ::
 (_new_cell, Gfun(Internal f_new_cell)) :: (_get, Gfun(Internal f_get)) ::
 (_incr_list, Gfun(Internal f_incr_list)) ::
 (_incr, Gfun(Internal f_incr)) :: (_incrx, Gfun(Internal f_incrx)) :: nil).

Definition public_idents : list ident :=
(_incrx :: _incr :: _incr_list :: _get :: _new_cell :: _new_table ::
 _copy_string :: _hash :: _strcmp :: _strcpy :: _strlen :: _exit ::
 _malloc :: ___builtin_debug :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_clsll :: ___builtin_clsl :: ___builtin_cls ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.



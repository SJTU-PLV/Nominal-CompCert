Require Import Valuesrel.
Require Import Globalenvs.
Require Import CKLR.
Require Import Builtins.

Notation builtin_sem_rel R :=
  ((|= Val.inject_list @@ [mi R] ++>
       k1 option_le (Val.inject @@ [mi R])) @@ (bs_sem _))%rel.

Global Instance builtin_function_sem_rel R:
  Monotonic (@builtin_function_sem) (forallr -, builtin_sem_rel R).
Proof.
  unfold builtin_function_sem.
  repeat rstep.
  - unfold standard_builtin_sem.
    destruct b; cbn; rauto.
  - unfold platform_builtin_sem.
    destruct b; cbn; rauto.
Qed.

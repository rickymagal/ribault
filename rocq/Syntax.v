From Coq Require Import ZArith.
From Coq Require Import String List.
Import ListNotations.

Definition ident := string.

Inductive binop : Type :=
| OAdd | OSub | OMul | ODiv | OMod
| OEq | ONe | OLt | OLe | OGt | OGe
| OAnd | OOr.

Inductive unop : Type := UNeg | UNot.

Inductive expr : Type :=
| EInt  (n : Z)
| EBool (b : bool)
| EVar  (x : ident)
| EUn   (u : unop) (e : expr)
| EBin  (o : binop) (e1 e2 : expr)
| EIf   (c t e : expr)
| ELet  (x : ident) (e1 e2 : expr)
| EApp  (f : ident) (args : list expr).

Record fundecl := { fd_name : ident; fd_params : list ident; fd_body : expr }.

Definition program := list fundecl.

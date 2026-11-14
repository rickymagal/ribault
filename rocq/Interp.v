From Coq Require Import String ZArith List Bool.
Import ListNotations.
From Ribault Require Import Syntax.
Local Open Scope Z_scope.

Inductive value : Type := VInt (n : Z) | VBool (b : bool).

Inductive result (A : Type) : Type := Ok (a : A) | Err | Abort | TimeOut.
Arguments Ok {A} a.
Arguments Err {A}.
Arguments Abort {A}.
Arguments TimeOut {A}.

Definition rbind {A B} (r : result A) (f : A -> result B) : result B :=
  match r with Ok a => f a | Err => Err | Abort => Abort | TimeOut => TimeOut end.
Notation "x <- e1 ;; e2" := (rbind e1 (fun x => e2))
  (right associativity, at level 60).

Definition venv := list (ident * value).

Fixpoint vlookup (env : venv) (x : ident) : option value :=
  match env with
  | [] => None
  | (y,v) :: r => if String.eqb x y then Some v else vlookup r x
  end.

Fixpoint flookup (p : program) (f : ident) : option fundecl :=
  match p with
  | [] => None
  | d :: r => if String.eqb f (fd_name d) then Some d else flookup r f
  end.

Definition eval_un (u : unop) (v : value) : result value :=
  match u, v with
  | UNeg, VInt n  => Ok (VInt (- n))
  | UNot, VBool b => Ok (VBool (negb b))
  | _, _          => Err
  end.

Definition eval_bin (o : binop) (v1 v2 : value) : result value :=
  match o, v1, v2 with
  | OAdd, VInt a, VInt b => Ok (VInt (a + b))
  | OSub, VInt a, VInt b => Ok (VInt (a - b))
  | OMul, VInt a, VInt b => Ok (VInt (a * b))
  | ODiv, VInt a, VInt b => if Z.eqb b 0 then Abort else Ok (VInt (Z.quot a b))
  | OMod, VInt a, VInt b => if Z.eqb b 0 then Abort else Ok (VInt (Z.rem a b))
  | OEq,  VInt a, VInt b => Ok (VBool (Z.eqb a b))
  | OEq,  VBool a,VBool b=> Ok (VBool (Bool.eqb a b))
  | ONe,  VInt a, VInt b => Ok (VBool (negb (Z.eqb a b)))
  | ONe,  VBool a,VBool b=> Ok (VBool (negb (Bool.eqb a b)))
  | OLt,  VInt a, VInt b => Ok (VBool (Z.ltb a b))
  | OLe,  VInt a, VInt b => Ok (VBool (Z.leb a b))
  | OGt,  VInt a, VInt b => Ok (VBool (Z.ltb b a))
  | OGe,  VInt a, VInt b => Ok (VBool (Z.leb b a))
  | OAnd, VBool a,VBool b=> Ok (VBool (andb a b))
  | OOr,  VBool a,VBool b=> Ok (VBool (orb a b))
  | _, _, _              => Err
  end.

Fixpoint eval (fuel : nat) (p : program) (env : venv) (e : expr)
  {struct fuel} : result value :=
  match fuel with
  | O => TimeOut
  | S fuel' =>
    match e with
    | EInt n  => Ok (VInt n)
    | EBool b => Ok (VBool b)
    | EVar x  => match vlookup env x with Some v => Ok v | None => Err end
    | EUn u e1 => v <- eval fuel' p env e1 ;; eval_un u v
    | EBin o e1 e2 =>
        v1 <- eval fuel' p env e1 ;;
        v2 <- eval fuel' p env e2 ;;
        eval_bin o v1 v2
    | EIf c t f =>
        vc <- eval fuel' p env c ;;
        match vc with
        | VBool true  => eval fuel' p env t
        | VBool false => eval fuel' p env f
        | _           => Err
        end
    | ELet x e1 e2 =>
        v <- eval fuel' p env e1 ;; eval fuel' p ((x,v)::env) e2
    | EApp f args =>
        match flookup p f with
        | None => Err
        | Some d =>
            vs <- (fix evargs (es : list expr) : result (list value) :=
                     match es with
                     | [] => Ok []
                     | e0 :: es' =>
                         v  <- eval fuel' p env e0 ;;
                         vs <- evargs es' ;;
                         Ok (v :: vs)
                     end) args ;;
            if Nat.eqb (length (fd_params d)) (length vs)
            then eval fuel' p (combine (fd_params d) vs) (fd_body d)
            else Err
        end
    end
  end.

From Coq Require Import String List Bool.
Import ListNotations.
From Ribault Require Import Syntax.

Inductive ty : Type := TInt | TBool.

Definition ty_eqb (a b : ty) : bool :=
  match a, b with
  | TInt, TInt => true
  | TBool, TBool => true
  | _, _ => false
  end.

Definition tenv := list (ident * ty).
Definition fsig := list (ident * (list ty * ty)).

Fixpoint tlookup (G : tenv) (x : ident) : option ty :=
  match G with
  | [] => None
  | (y,t) :: r => if String.eqb x y then Some t else tlookup r x
  end.

Fixpoint flookup_sig (Sg : fsig) (f : ident) : option (list ty * ty) :=
  match Sg with
  | [] => None
  | (g,s) :: r => if String.eqb f g then Some s else flookup_sig r f
  end.

Definition ty_un (u : unop) (t : ty) : option ty :=
  match u, t with
  | UNeg, TInt  => Some TInt
  | UNot, TBool => Some TBool
  | _, _        => None
  end.

Definition ty_bin (o : binop) (t1 t2 : ty) : option ty :=
  match o with
  | OAdd => match t1, t2 with TInt, TInt => Some TInt | _, _ => None end
  | OSub => match t1, t2 with TInt, TInt => Some TInt | _, _ => None end
  | OMul => match t1, t2 with TInt, TInt => Some TInt | _, _ => None end
  | ODiv => match t1, t2 with TInt, TInt => Some TInt | _, _ => None end
  | OMod => match t1, t2 with TInt, TInt => Some TInt | _, _ => None end
  | OLt  => match t1, t2 with TInt, TInt => Some TBool | _, _ => None end
  | OLe  => match t1, t2 with TInt, TInt => Some TBool | _, _ => None end
  | OGt  => match t1, t2 with TInt, TInt => Some TBool | _, _ => None end
  | OGe  => match t1, t2 with TInt, TInt => Some TBool | _, _ => None end
  | OEq  => match t1, t2 with TInt, TInt => Some TBool | TBool, TBool => Some TBool | _, _ => None end
  | ONe  => match t1, t2 with TInt, TInt => Some TBool | TBool, TBool => Some TBool | _, _ => None end
  | OAnd => match t1, t2 with TBool, TBool => Some TBool | _, _ => None end
  | OOr  => match t1, t2 with TBool, TBool => Some TBool | _, _ => None end
  end.

Fixpoint tc (Sg : fsig) (G : tenv) (e : expr) {struct e} : option ty :=
  match e with
  | EInt _  => Some TInt
  | EBool _ => Some TBool
  | EVar x  => tlookup G x
  | EUn u e1 =>
      match tc Sg G e1 with Some t => ty_un u t | None => None end
  | EBin o e1 e2 =>
      match tc Sg G e1, tc Sg G e2 with
      | Some t1, Some t2 => ty_bin o t1 t2
      | _, _ => None
      end
  | EIf ec et ee =>
      match tc Sg G ec with
      | Some TBool =>
          match tc Sg G et, tc Sg G ee with
          | Some tthen, Some telse =>
              if ty_eqb tthen telse then Some tthen else None
          | _, _ => None
          end
      | _ => None
      end
  | ELet x e1 e2 =>
      match tc Sg G e1 with
      | Some t1 => tc Sg ((x,t1) :: G) e2
      | None => None
      end
  | EApp f args =>
      match flookup_sig Sg f with
      | Some (ptys, rt) =>
          if (fix check_args (es : list expr) (ts : list ty) : bool :=
                match es, ts with
                | [], [] => true
                | e0 :: es', t0 :: ts' =>
                    match tc Sg G e0 with
                    | Some t => andb (ty_eqb t t0) (check_args es' ts')
                    | None => false
                    end
                | _, _ => false
                end) args ptys
          then Some rt else None
      | None => None
      end
  end.

Definition wt_fundecl (Sg : fsig) (d : fundecl) : bool :=
  match flookup_sig Sg (fd_name d) with
  | Some (ptys, rt) =>
      andb (Nat.eqb (length (fd_params d)) (length ptys))
           (match tc Sg (combine (fd_params d) ptys) (fd_body d) with
            | Some t => ty_eqb t rt
            | None => false
            end)
  | None => false
  end.

Definition wt_program (Sg : fsig) (p : program) : bool :=
  forallb (wt_fundecl Sg) p.

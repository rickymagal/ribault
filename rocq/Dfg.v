From Coq Require Import String ZArith List Bool.
Import ListNotations.
From Ribault Require Import Syntax Interp.
Local Open Scope string_scope.

(* core node, mirroring the Node.hs subset *)
Inductive node :=
| DConst (n : Z)
| DBoolC (b : bool)
| DBin   (o : binop)     (* inputs on ports "0" and "1" *)
| DUn    (u : unop)      (* input on port "0" *)
| DSteer                 (* guard on "g", value on "v", outputs "t"/"f" *)
| DIf                    (* guard on "g", then taken branch on "t"/"f" (demand-driven) *)
| DArg   (x : ident).    (* formal argument, read from the environment *)

Definition nodeid := nat.
Definition portid := string.

Record dfg := {
  dnodes : list (nodeid * node);
  dedges : list (nodeid * portid * nodeid * portid)  (* src, sport, tgt, tport *)
}.

Fixpoint lookup_node (ns : list (nodeid * node)) (i : nodeid) : option node :=
  match ns with
  | [] => None
  | (j,nd) :: r => if Nat.eqb i j then Some nd else lookup_node r i
  end.

(* source feeding port (tgt,tport): the first matching edge *)
Fixpoint feeder (es : list (nodeid * portid * nodeid * portid))
                (tgt : nodeid) (tport : portid) : option (nodeid * portid) :=
  match es with
  | [] => None
  | (s,sp,t,tp) :: r =>
      if andb (Nat.eqb t tgt) (String.eqb tp tport)
      then Some (s, sp) else feeder r tgt tport
  end.

(* the environment lookup is Interp.vlookup *)
Fixpoint eval_dfg (fuel : nat) (g : dfg) (env : venv)
                  (nid : nodeid) (port : portid) {struct fuel} : result value :=
  match fuel with
  | O => TimeOut
  | S fuel' =>
    let resolve p :=
        match feeder (dedges g) nid p with
        | Some (s, sp) => eval_dfg fuel' g env s sp
        | None => Err
        end in
    match lookup_node (dnodes g) nid with
    | None => Err
    | Some nd =>
      match nd with
      | DConst n => Ok (VInt n)
      | DBoolC b => Ok (VBool b)
      | DArg x   => match vlookup env x with Some v => Ok v | None => Err end
      | DUn u    => v <- resolve "0" ;; eval_un u v
      | DBin o   => a <- resolve "0" ;; b <- resolve "1" ;; eval_bin o a b
      | DSteer   =>
          g0 <- resolve "g" ;;
          v  <- resolve "v" ;;
          match g0 with
          | VBool true  => if String.eqb port "t" then Ok v else Err
          | VBool false => if String.eqb port "f" then Ok v else Err
          | _ => Err
          end
      | DIf      =>
          g0 <- resolve "g" ;;
          match g0 with
          | VBool true  => resolve "t"
          | VBool false => resolve "f"
          | _           => Err
          end
      end
    end
  end.

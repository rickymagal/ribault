From Coq Require Import String ZArith List Bool.
Import ListNotations.
From Ribault Require Import Syntax Interp Dfg.
Local Open Scope string_scope.

(* ===== fragment this translation covers faithfully =====
   straight-line = combinational, with no control and no call.
   EIf/EApp need steer/merge and the exec protocol; they stay
   out, and preservation (next WO) only quantifies over
   straight_line e = true. *)
Fixpoint straight_line (e : expr) : bool :=
  match e with
  | EInt _  => true
  | EBool _ => true
  | EVar _  => true
  | EUn _ e1      => straight_line e1
  | EBin _ e1 e2  => straight_line e1 && straight_line e2
  | ELet _ e1 e2  => straight_line e1 && straight_line e2
  | EIf _ _ _     => false
  | EApp _ _      => false
  end.

(* compilation environment: a variable bound by let/param -> the
   node that produces its value. A let-bound variable becomes an
   edge (fan-out, no new node); a free parameter becomes a DArg
   leaf, read from env at eval_dfg time. *)
Definition cenv := list (ident * nodeid).

Fixpoint clookup (r : cenv) (x : ident) : option nodeid :=
  match r with
  | [] => None
  | (y,i) :: r' => if String.eqb x y then Some i else clookup r' x
  end.

(* canonical output port of any combinational node. The demanded
   port is ignored by every node other than DSteer, so "0" at the
   source of an edge between straight-line nodes is irrelevant to
   eval_dfg; only the if WO will use "t"/"f" at the source. *)
Definition oport : portid := "0".

(* trans k ns es rho e = (next_fresh_id, nodes', edges', output_node).
   k is the fresh-id counter; ns/es accumulate nodes and edges;
   rho binds variables to node ids. Structural in e. *)
Fixpoint trans (k : nat) (ns : list (nodeid * node))
               (es : list (nodeid * portid * nodeid * portid))
               (rho : cenv) (e : expr)
  : nat * list (nodeid * node)
        * list (nodeid * portid * nodeid * portid) * nodeid :=
  match e with
  | EInt n  => (S k, (k, DConst n) :: ns, es, k)
  | EBool b => (S k, (k, DBoolC b) :: ns, es, k)
  | EVar x  =>
      match clookup rho x with
      | Some i => (k, ns, es, i)                    (* bound: reuse the producer node *)
      | None   => (S k, (k, DArg x) :: ns, es, k)   (* free: DArg leaf *)
      end
  | EUn u e1 =>
      let '(k1, ns1, es1, o1) := trans k ns es rho e1 in
      (S k1, (k1, DUn u) :: ns1,
             (o1, oport, k1, "0") :: es1, k1)
  | EBin o e1 e2 =>
      let '(k1, ns1, es1, o1) := trans k  ns  es  rho e1 in
      let '(k2, ns2, es2, o2) := trans k1 ns1 es1 rho e2 in
      (S k2, (k2, DBin o) :: ns2,
             (o1, oport, k2, "0") :: (o2, oport, k2, "1") :: es2, k2)
  | ELet x e1 e2 =>
      let '(k1, ns1, es1, o1) := trans k ns es rho e1 in
      trans k1 ns1 es1 ((x, o1) :: rho) e2
  | EIf  _ _ _ => (S k, (k, DConst 0) :: ns, es, k)  (* control: dedicated WO *)
  | EApp _ _   => (S k, (k, DConst 0) :: ns, es, k)  (* call: dedicated WO *)
  end.

Definition translate (e : expr) : dfg * nodeid :=
  let '(_, ns, es, out) := trans 0 [] [] [] e in
  ({| dnodes := ns; dedges := es |}, out).

(* smoke tests: the wiring agrees with eval_dfg by computation. *)
Example trans_add :
  let '(g, out) := translate (EBin OAdd (EInt 1) (EInt 2)) in
  eval_dfg 10 g [] out "0" = Ok (VInt 3).
Proof. vm_compute. reflexivity. Qed.

(* let x = 2+3 in x*x  ->  25 ; EVar reuses the add node (fan-out) *)
Example trans_let_share :
  let '(g, out) :=
    translate (ELet "x" (EBin OAdd (EInt 2) (EInt 3))
                        (EBin OMul (EVar "x") (EVar "x"))) in
  eval_dfg 20 g [] out "0" = Ok (VInt 25).
Proof. vm_compute. reflexivity. Qed.
